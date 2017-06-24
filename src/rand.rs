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

use gmp_mpfr_sys::gmp::{self, randstate_t};
use inner::{Inner, InnerMut};
use integer::Integer;
use std::marker::PhantomData;
use std::mem;
use std::os::raw::{c_ulong, c_void};

/// The state of a random number generator.
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
                inner: inner,
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
    #[inline]
    pub fn new() -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_default(&mut inner);
            RandState {
                inner: inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a random generator with a Mersenne Twister algorithm.
    pub fn new_mersenne_twister() -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_mt(&mut inner);
            RandState {
                inner: inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm *X* = (*a* × *X* + *c*) mod 2<sup>`bits`</sup>.
    pub fn new_linear_congruential(
        a: &Integer,
        c: u32,
        bits: u32,
    ) -> RandState<'a> {
        unsafe {
            let mut inner = mem::uninitialized();
            gmp::randinit_lc_2exp(&mut inner, a.inner(), c.into(), bits.into());
            RandState {
                inner: inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm like the [`new_linear_congruential`][cong] method.
    ///
    /// *a*, *c* and `bits` are selected from a table such that at
    /// least `size` bits of each *X* will be used, that is
    /// 2<sup>`bits`</sup> ≥ `size`. The table only has values for a
    /// size of up to 256 bits; `None` will be returned if the
    /// requested size is larger.
    ///
    /// [cong]: #method.new_linear_congruential
    pub fn new_linear_congruential_size(size: u32) -> Option<RandState<'a>> {
        unsafe {
            let mut inner = mem::uninitialized();
            if gmp::randinit_lc_2exp_size(&mut inner, size.into()) != 0 {
                Some(RandState {
                    inner: inner,
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
    /// i.random_below(&mut rand);
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
    #[inline]
    pub fn seed(&mut self, seed: &Integer) {
        unsafe {
            gmp::randseed(self.inner_mut(), seed.inner());
        }
    }

    /// Generates a random number with the specified number of bits.
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
pub trait RandGen: Send + Sync {
    /// Gets a random 32-bit unsigned integer.
    fn gen(&mut self) -> u32;

    /// Seeds the random number generator.
    ///
    /// The default implementation of this function does nothing.
    ///
    /// Note that the [`RandState::seed()][seed] method will pass its
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
    _get: Option<
        unsafe extern "C" fn(*mut randstate_t,
                             *mut gmp::limb_t,
                             c_ulong),
    >,
    _clear: Option<unsafe extern "C" fn(*mut randstate_t)>,
    _iset: Option<unsafe extern "C" fn(*mut randstate_t, *const randstate_t)>,
}

unsafe extern "C" fn custom_seed(s: *mut randstate_t, seed: *const gmp::mpz_t) {
    let s_ptr = s as *mut MpRandState;
    let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
    (*r_ptr).seed(&(*(seed as *const Integer)));
}

unsafe extern "C" fn custom_get(
    s: *mut randstate_t,
    limb: *mut gmp::limb_t,
    bits: c_ulong,
) {
    let s_ptr = s as *mut MpRandState;
    let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
    let gen = || (*r_ptr).gen();
    match gmp::LIMB_BITS {
        64 => {
            let (limbs, rest) = (bits / 64, bits % 64);
            assert_eq!((limbs + 1) as isize as c_ulong, limbs + 1, "overflow");
            let limbs = limbs as isize;
            for i in 0..limbs {
                let n = (gen() as u64) | (gen() as u64) << 32;
                *(limb.offset(i)) = n as gmp::limb_t;
            }
            if rest >= 32 {
                let mut n = gen() as u64;
                if rest > 32 {
                    let mask = !(!0 << (rest - 32));
                    n |= ((gen() & mask) as u64) << 32;
                }
                *(limb.offset(limbs)) = n as gmp::limb_t;
            } else if rest > 0 {
                let mask = !(!0 << rest);
                let n = (gen() & mask) as u64;
                *(limb.offset(limbs)) = n as gmp::limb_t;
            }
        }
        32 => {
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
        _ => unimplemented!(),
    }
}

unsafe extern "C" fn custom_clear(s: *mut randstate_t) {
    let s_ptr = s as *mut MpRandState;
    let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
    drop(Box::from_raw(r_ptr));
}

unsafe extern "C" fn custom_iset(
    _s: *mut randstate_t,
    _src: *const randstate_t,
) {
    panic!("cannot clone custom Rand");
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
