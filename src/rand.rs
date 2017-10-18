// Copyright © 2017 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <http://www.gnu.org/licenses/>.

//! Random number generation.

use Integer;
use inner::{Inner, InnerMut};

use gmp_mpfr_sys::gmp::{self, randstate_t};
use std::marker::PhantomData;
use std::mem;
use std::os::raw::{c_ulong, c_void};
use std::panic::{self, AssertUnwindSafe};
use std::process;

/// The state of a random number generator.
///
/// # Examples
///
/// ```rust
/// use rug::rand::RandState;
/// let mut rand = RandState::new();
/// let u = rand.bits(32);
/// println!("32 random bits: {:032b}", u);
/// ```
pub struct RandState<'a> {
    inner: randstate_t,
    phantom: PhantomData<&'a RandGen>,
}

impl<'a> Default for RandState<'a> {
    #[inline]
    fn default() -> RandState<'a> {
        RandState::new()
    }
}

impl<'a> Clone for RandState<'a> {
    #[inline]
    fn clone(&self) -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_set(&mut inner, self.inner());
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }
}

impl<'a> Drop for RandState<'a> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::randclear(self.inner_mut());
        }
    }
}

unsafe impl<'a> Send for RandState<'a> {}
unsafe impl<'a> Sync for RandState<'a> {}

impl<'a> RandState<'a> {
    /// Creates a new random generator with a compromise between speed
    /// and randomness.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    #[inline]
    pub fn new() -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_default(&mut inner);
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a random generator with a Mersenne Twister algorithm.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new_mersenne_twister();
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    pub fn new_mersenne_twister() -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_mt(&mut inner);
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm *X* = (*a* × *X* + *c*) mod 2<sup>*bits*</sup>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let a = match Integer::from_str_radix("292787ebd3329ad7e7575e2fd", 16) {
    ///     Ok(i) => i,
    ///     Err(_) => unreachable!(),
    /// };
    /// let c = 1;
    /// let bits = 100;
    /// let mut rand = RandState::new_linear_congruential(&a, c, bits);
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    pub fn new_linear_congruential(
        a: &Integer,
        c: u32,
        bits: u32,
    ) -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_lc_2exp(&mut inner, a.inner(), c.into(), bits.into());
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm like the [`new_linear_congruential`][cong] method.
    ///
    /// For the linear congrentail algorithm *X* = (*a* × *X* + *c*)
    /// mod 2<sup>*bits*</sup>, *a*, *c* and *bits* are selected from
    /// a table such that at least *size* bits of each *X* will be
    /// used, that is *bits* ≥ *size*. The table only has values for a
    /// size of up to 256 bits; `None` will be returned if the
    /// requested size is larger.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = match RandState::new_linear_congruential_size(100) {
    ///     Some(r) => r,
    ///     None => unreachable!(),
    /// };
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    ///
    /// [cong]: #method.new_linear_congruential
    pub fn new_linear_congruential_size(size: u32) -> Option<RandState<'a>> {
        unsafe {
            let mut inner = mem::uninitialized();
            if gmp::randinit_lc_2exp_size(&mut inner, size.into()) != 0 {
                Some(RandState {
                    inner,
                    phantom: PhantomData,
                })
            } else {
                None
            }
        }
    }

    /// Creates a new custom random generator.
    ///
    /// The created `RandState` is borrowing mutably, so unlike other
    /// instances of `RandState`, it cannot be cloned; attempting to
    /// clone will panic.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::{RandGen, RandState};
    /// struct Seed;
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 { 0x8cef7310 }
    /// }
    /// let mut seed = Seed;
    /// let mut rand = RandState::new_custom(&mut seed);
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 <= {} < 15", i);
    /// assert!(i < 15);
    /// ```
    pub fn new_custom<'c, T>(custom: &mut T) -> RandState<'c>
    where
        T: 'c + RandGen,
    {
        let b = Box::new(custom as &mut RandGen);
        let r_ptr = Box::into_raw(b);
        let inner = MpRandState {
            seed: gmp::mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut gmp::limb_t,
            },
            _alg: RandAlg::_DEFAULT,
            _algdata: &CUSTOM_FUNCS as *const _ as *mut _,
        };
        RandState {
            inner: unsafe { mem::transmute(inner) },
            phantom: PhantomData,
        }
    }

    /// Seeds the random generator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let seed = Integer::from(123456);
    /// let mut rand = RandState::new();
    /// rand.seed(&seed);
    /// let u1a = rand.bits(32);
    /// let u1b = rand.bits(32);
    /// // reseed with the same seed
    /// rand.seed(&seed);
    /// let u2a = rand.bits(32);
    /// let u2b = rand.bits(32);
    /// assert_eq!(u1a, u2a);
    /// assert_eq!(u1b, u2b);
    /// ```
    #[inline]
    pub fn seed(&mut self, seed: &Integer) {
        unsafe {
            gmp::randseed(self.inner_mut(), seed.inner());
        }
    }

    /// Generates a random number with the specified number of bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let u = rand.bits(16);
    /// assert!(u < (1 << 16));
    /// println!("16 random bits: {:016b}", u);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `bits` is greater than 32.
    #[inline]
    pub fn bits(&mut self, bits: u32) -> u32 {
        assert!(bits <= 32, "bits out of range");
        unsafe { gmp::urandomb_ui(self.inner_mut(), bits.into()) as u32 }
    }

    /// Generates a random number below the given boundary value.
    ///
    /// This function can never return the maximum 32-bit value; in
    /// order to generate a 32-bit random value that covers the whole
    /// range, use the [`bits`](#method.bits) method with `bits` set
    /// to 32.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let u = rand.below(10000);
    /// assert!(u < 10000);
    /// println!("0 ≤ {} < 10000", u);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is zero.
    #[inline]
    pub fn below(&mut self, bound: u32) -> u32 {
        assert_ne!(bound, 0, "cannot be below zero");
        unsafe { gmp::urandomm_ui(self.inner_mut(), bound.into()) as u32 }
    }
}

/// Custom random number generator to be used with
/// [`RandState`](struct.RandState.html).
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::rand::RandGen;
/// struct SimpleGenerator {
///     seed: u64,
/// }
/// impl RandGen for SimpleGenerator {
///     fn gen(&mut self) -> u32 {
///         self.seed =
///             self.seed.wrapping_mul(6364136223846793005).wrapping_add(1);
///         (self.seed >> 32) as u32
///     }
///     fn seed(&mut self, seed: &Integer) {
///         self.seed = seed.to_u64_wrapping();
///     }
/// }
/// let mut rand = SimpleGenerator { seed: 1 };
/// assert_eq!(rand.gen(), 1481765933);
/// assert_eq!(rand.seed, 6364136223846793006);
/// ```
pub trait RandGen: Send + Sync {
    /// Gets a random 32-bit unsigned integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandGen;
    /// struct SimpleGenerator {
    ///     seed: u64,
    /// }
    /// impl RandGen for SimpleGenerator {
    ///     fn gen(&mut self) -> u32 {
    ///         self.seed =
    ///             self.seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    ///         (self.seed >> 32) as u32
    ///     }
    /// }
    /// let mut rand = SimpleGenerator { seed: 1 };
    /// let first = rand.gen();
    /// assert_eq!(rand.seed, 6364136223846793006);
    /// assert_eq!(first, 1481765933);
    /// let second = rand.gen();
    /// assert_eq!(rand.seed, 13885033948157127959);
    /// assert_eq!(second, 3232861391);
    /// ```
    fn gen(&mut self) -> u32;

    /// Seeds the random number generator.
    ///
    /// The default implementation of this function does nothing.
    ///
    /// Note that the [RandState::seed()][seed] method will pass its
    /// seed parameter exactly to this function without using it
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rand::{RandGen, RandState};
    /// struct Seed { inner: Integer };
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 { self.inner.to_u32_wrapping() }
    ///     fn seed(&mut self, seed: &Integer) {
    ///         self.inner.assign(seed);
    ///     }
    /// }
    /// let mut seed = Seed { inner: Integer::from(12) };
    /// let i = Integer::from(12345);
    /// {
    ///     let mut rand = RandState::new_custom(&mut seed);
    ///     rand.seed(&i);
    /// }
    /// assert_eq!(seed.inner, i);
    /// ```
    ///
    /// If you use unsafe code, you can pass a reference to anything,
    /// or even an `isize` or `usize`, to the seeding function.
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::{RandGen, RandState};
    /// struct Seed { num: isize };
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 { 0x8cef7310 }
    ///     fn seed(&mut self, seed: &Integer) {
    ///         // cast seed to pointer, then to isize
    ///         self.num = seed as *const _ as isize;
    ///     }
    /// }
    /// let mut seed = Seed { num: 15 };
    /// let i = -12345_isize;
    /// {
    ///     let i_ptr = i as *const Integer;
    ///     // unsafe code to cast i from isize to &Integer
    ///     let ir = unsafe { &*i_ptr };
    ///     let mut rand = RandState::new_custom(&mut seed);
    ///     rand.seed(ir);
    /// }
    /// assert_eq!(seed.num, i);
    /// ```
    ///
    /// [seed]: struct.RandState.html#method.seed
    #[inline]
    fn seed(&mut self, _seed: &Integer) {}
}

// The contents of gmp::randstate_t are not available because the
// internal details of gmp_randstate_t are not documented by GMP. So
// we duplcate them here. The structure of function pointers
// gmp_randfnptr_t is only inside gmp-impl.h and is not available
// externally, so we duplicate it here as well.
#[repr(C)]
enum RandAlg {
    _DEFAULT = 0,
}

#[repr(C)]
struct MpRandState {
    seed: gmp::mpz_t,
    _alg: RandAlg,
    _algdata: *mut c_void,
}

#[repr(C)]
struct Funcs {
    _seed: Option<unsafe extern "C" fn(*mut randstate_t, *const gmp::mpz_t)>,
    _get:
        Option<
            unsafe extern "C" fn(*mut randstate_t, *mut gmp::limb_t, c_ulong),
        >,
    _clear: Option<unsafe extern "C" fn(*mut randstate_t)>,
    _iset: Option<unsafe extern "C" fn(*mut randstate_t, *const randstate_t)>,
}

macro_rules! c_callback {
    { $(fn $func:ident($($param:tt)*) $body:block)* } => {
        $(
            unsafe extern "C" fn $func($($param)*) {
                panic::catch_unwind(AssertUnwindSafe(|| $body))
                    .unwrap_or_else(|_| process::abort())
            }
        )*
    }
}

c_callback! {
    fn custom_seed(s: *mut randstate_t, seed: *const gmp::mpz_t) {
        let s_ptr = s as *mut MpRandState;
        let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
        (*r_ptr).seed(&(*(seed as *const Integer)));
    }

    fn custom_get(
        s: *mut randstate_t,
        limb: *mut gmp::limb_t,
        bits: c_ulong,
    ) {
        let s_ptr = s as *mut MpRandState;
        let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
        let gen = || (*r_ptr).gen();
        #[cfg(gmp_limb_bits_64)]
        {
            let (limbs, rest) = (bits / 64, bits % 64);
            assert_eq!((limbs + 1) as isize as c_ulong, limbs + 1, "overflow");
            let limbs = limbs as isize;
            for i in 0..limbs {
                let n = u64::from(gen()) | u64::from(gen()) << 32;
                *(limb.offset(i)) = n as gmp::limb_t;
            }
            if rest >= 32 {
                let mut n = u64::from(gen());
                if rest > 32 {
                    let mask = !(!0 << (rest - 32));
                    n |= u64::from(gen() & mask) << 32;
                }
                *(limb.offset(limbs)) = n as gmp::limb_t;
            } else if rest > 0 {
                let mask = !(!0 << rest);
                let n = u64::from(gen() & mask);
                *(limb.offset(limbs)) = n as gmp::limb_t;
            }
        }
        #[cfg(gmp_limb_bits_32)]
        {
            let (limbs, rest) = (bits / 32, bits % 32);
            assert_eq!((limbs + 1) as isize as c_ulong, limbs + 1, "overflow");
            let limbs = limbs as isize;
            for i in 0..limbs {
                *(limb.offset(i)) = gen() as gmp::limb_t;
            }
            if rest > 0 {
                let mask = !(!0 << rest);
                *(limb.offset(limbs)) = (gen() & mask) as gmp::limb_t;
            }
        }
    }

    fn custom_clear(s: *mut randstate_t) {
        let s_ptr = s as *mut MpRandState;
        let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
        drop(Box::from_raw(r_ptr));
    }

    fn custom_iset(_s: *mut randstate_t, _src: *const randstate_t) {
        panic!("cannot clone custom Rand");
    }
}

const CUSTOM_FUNCS: Funcs = Funcs {
    _seed: Some(custom_seed),
    _get: Some(custom_get),
    _clear: Some(custom_clear),
    _iset: Some(custom_iset),
};

impl<'a> Inner for RandState<'a> {
    type Output = randstate_t;
    #[inline]
    fn inner(&self) -> &randstate_t {
        &self.inner
    }
}

impl<'a> InnerMut for RandState<'a> {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut randstate_t {
        &mut self.inner
    }
}
