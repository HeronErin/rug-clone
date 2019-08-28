// Copyright © 2016–2019 University of Malta

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
// this program. If not, see <https://www.gnu.org/licenses/>.

/*!
Random number generation.
*/

// UNDEFINED BEHAVIOR WARNING:
//
// Not all the fields of randstate_t are used, and thus GMP does not
// initialize all the fields. So we must use zeroed rather than
// uninitialized memory, otherwise we may be left with uninitialized
// memory which can eventually lead to undefined behavior.

use crate::{cast, Integer};
use gmp_mpfr_sys::gmp::{self, randstate_t};
#[cfg(not(ffi_panic_aborts))]
use std::panic::{self, AssertUnwindSafe};
use std::{
    marker::PhantomData,
    mem,
    os::raw::{c_ulong, c_void},
    process, ptr,
};

/**
The state of a random number generator.

# Examples

```rust
use rug::rand::RandState;
let mut rand = RandState::new();
let u = rand.bits(32);
println!("32 random bits: {:032b}", u);
```
*/
#[repr(transparent)]
pub struct RandState<'a> {
    inner: randstate_t,
    phantom: PhantomData<&'a dyn RandGen>,
}

impl Default for RandState<'_> {
    #[inline]
    fn default() -> RandState<'static> {
        RandState::new()
    }
}

impl Clone for RandState<'_> {
    #[inline]
    fn clone(&self) -> RandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner: randstate_t, inner_ptr);
            gmp::randinit_set(inner_ptr, self.as_raw());
            // If d is null, then boxed_clone must have returned None.
            let inner = assume_init!(inner);
            if inner.seed.d.is_null() {
                panic!("`RandGen::boxed_clone` returned `None`");
            }
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }
}

impl Drop for RandState<'_> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::randclear(self.as_raw_mut());
        }
    }
}

unsafe impl Send for RandState<'_> {}
unsafe impl Sync for RandState<'_> {}

impl RandState<'_> {
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
    pub fn new() -> RandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner, inner_ptr);
            gmp::randinit_default(inner_ptr);
            let inner = assume_init!(inner);
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
    pub fn new_mersenne_twister() -> RandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner, inner_ptr);
            gmp::randinit_mt(inner_ptr);
            let inner = assume_init!(inner);
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>) mod 2<sup><i>bits</i></sup>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{rand::RandState, Integer};
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
    pub fn new_linear_congruential(a: &Integer, c: u32, bits: u32) -> RandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner, inner_ptr);
            gmp::randinit_lc_2exp(inner_ptr, a.as_raw(), c.into(), bits.into());
            let inner = assume_init!(inner);
            RandState {
                inner,
                phantom: PhantomData,
            }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm like the [`new_linear_congruential`] method.
    ///
    /// For the linear congrentail algorithm <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>)
    /// mod 2<sup><i>bits</i></sup>, <i>a</i>, <i>c</i> and <i>bits</i> are selected from
    /// a table such that at least <i>size</i> bits of each <i>X</i> will be
    /// used, that is <i>bits</i> ≥ <i>size</i>. The table only has values for a
    /// size of up to 256 bits; [`None`] will be returned if the
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
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    /// [`new_linear_congruential`]: #method.new_linear_congruential
    pub fn new_linear_congruential_size(size: u32) -> Option<RandState<'static>> {
        unsafe {
            let_zeroed_ptr!(inner, inner_ptr);
            if gmp::randinit_lc_2exp_size(inner_ptr, size.into()) != 0 {
                let inner = assume_init!(inner);
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
    /// If the custom random generator is cloned, the implemented
    /// trait method [`RandGen::boxed_clone`] is called; this leads to
    /// panic if the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{RandGen, RandState},
    ///     Integer,
    /// };
    /// struct Seed;
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         0x8cef7310
    ///     }
    /// }
    /// let mut seed = Seed;
    /// let mut rand = RandState::new_custom(&mut seed);
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 ≤ {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    /// [`RandGen::boxed_clone`]: trait.RandGen.html#method.boxed_clone
    pub fn new_custom(custom: &mut dyn RandGen) -> RandState<'_> {
        let b: Box<&mut dyn RandGen> = Box::new(custom);
        let r_ptr: *mut &mut dyn RandGen = Box::into_raw(b);
        let inner = randstate_t {
            seed: gmp::mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut gmp::limb_t,
            },
            alg: 0,
            algdata: &CUSTOM_FUNCS as *const Funcs as *mut c_void,
        };
        RandState {
            inner,
            phantom: PhantomData,
        }
    }

    /// Creates a new custom random generator.
    ///
    /// If the custom random generator is cloned, the implemented
    /// trait method [`RandGen::boxed_clone`] is called;
    /// this leads to panic if the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{RandGen, RandState},
    ///     Integer,
    /// };
    /// struct Seed;
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         0x8cef7310
    ///     }
    /// }
    /// let seed = Box::new(Seed);
    /// let mut rand = RandState::new_custom_boxed(seed);
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 ≤ {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    /// [`RandGen::boxed_clone`]: trait.RandGen.html#method.boxed_clone
    pub fn new_custom_boxed(custom: Box<dyn RandGen>) -> RandState<'static> {
        let b: Box<Box<dyn RandGen>> = Box::new(custom);
        let r_ptr: *mut Box<dyn RandGen> = Box::into_raw(b);
        let inner = randstate_t {
            seed: gmp::mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut gmp::limb_t,
            },
            alg: 0,
            algdata: &CUSTOM_BOXED_FUNCS as *const Funcs as *mut c_void,
        };
        RandState {
            inner,
            phantom: PhantomData,
        }
    }

    /// Creates a random generator from an initialized
    /// [GMP random generator][`randstate_t`].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized. Note that the GMP functions
    ///     do not initialize all fields of the
    ///     [`gmp_mpfr_sys::gmp::randstate_t`][`randstate_t`] object,
    ///     which can eventually lead to reading uninitialized memory,
    ///     and that is undefined behaviour in Rust even if no
    ///     decision is made using the read value. One way to ensure
    ///     that there is no uninitialized memory inside `raw` is to
    ///     use [`MaybeUninit::zeroed`] to initialize `raw` before
    ///     initializing with a function such as
    ///     [`gmp_mpfr_sys::gmp::randinit_default`][`randinit_default`],
    ///     like in the example below.
    ///   * The [`gmp_mpfr_sys::gmp::randstate_t`][`randstate_t`] type
    ///     can be considered as a kind of pointer, so there can be
    ///     multiple copies of it. Since this function takes over
    ///     ownership, no other copies of the passed value should
    ///     exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #![cfg_attr(nightly_maybe_uninit, feature(maybe_uninit))]
    /// # fn main() {
    /// # #[cfg(maybe_uninit)] {
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::RandState;
    /// use std::mem::MaybeUninit;
    /// let mut rand = unsafe {
    ///     // Do not use MabyeUninit::uninit, as gmp::randinit_default
    ///     // does not initialize all of the fields of raw.
    ///     let mut raw = MaybeUninit::zeroed();
    ///     gmp::randinit_default(raw.as_mut_ptr());
    ///     let raw = raw.assume_init();
    ///     // raw is initialized and unique
    ///     RandState::from_raw(raw)
    /// };
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// // since rand is a RandState now, deallocation is automatic
    /// # }
    /// # }
    /// ```
    ///
    /// [`MaybeUninit::zeroed`]: https://doc.rust-lang.org/nightly/std/mem/union.MaybeUninit.html#method.zeroed
    /// [`randinit_default`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/fn.randinit_default.html
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub unsafe fn from_raw(raw: randstate_t) -> RandState<'static> {
        RandState {
            inner: raw,
            phantom: PhantomData,
        }
    }

    /// Converts a random generator into a
    /// [GMP random generator][`randstate_t`].
    ///
    /// The returned object should be freed to avoid memory leaks.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::RandState;
    /// let rand = RandState::new();
    /// let mut raw = rand.into_raw();
    /// unsafe {
    ///     let u = gmp::urandomb_ui(&mut raw, 32) as u32;
    ///     println!("32 random bits: {:032b}", u);
    ///     // free object to prevent memory leak
    ///     gmp::randclear(&mut raw);
    /// }
    /// ```
    ///
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn into_raw(self) -> randstate_t {
        let ret = self.inner;
        mem::forget(self);
        ret
    }

    /// Returns a pointer to the inner
    /// [GMP random generator][`randstate_t`].
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let raw_ptr = rand.as_raw();
    /// // There is not much you can do with an immutable randstate_t pointer.
    /// println!("pointer: {:p}", raw_ptr);
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    ///
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn as_raw(&self) -> *const randstate_t {
        &self.inner
    }

    /// Returns an unsafe mutable pointer to the inner
    /// [GMP random generator][`randstate_t`].
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let raw_ptr = rand.as_raw_mut();
    /// unsafe {
    ///     let u1 = gmp::urandomb_ui(raw_ptr, 32) as u32;
    ///     println!("32 random bits: {:032b}", u1);
    /// }
    /// let u2 = rand.bits(32);
    /// println!("another 32 random bits: {:032b}", u2);
    /// ```
    ///
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut randstate_t {
        &mut self.inner
    }

    /// Seeds the random generator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{rand::RandState, Integer};
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
            gmp::randseed(self.as_raw_mut(), seed.as_raw());
        }
    }

    /// Generates a random number with the specified number of bits.
    ///
    /// # Panics
    ///
    /// Panics if `bits` is greater than 32.
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
    #[inline]
    pub fn bits(&mut self, bits: u32) -> u32 {
        assert!(bits <= 32, "bits out of range");
        unsafe { gmp::urandomb_ui(self.as_raw_mut(), bits.into()) as u32 }
    }

    /// Generates a random number below the given boundary value.
    ///
    /// This function can never return the maximum 32-bit value; in
    /// order to generate a 32-bit random value that covers the whole
    /// range, use the [`bits`] method with `bits` set to 32.
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is zero.
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
    /// [`bits`]: #method.bits
    #[inline]
    pub fn below(&mut self, bound: u32) -> u32 {
        assert_ne!(bound, 0, "cannot be below zero");
        unsafe { gmp::urandomm_ui(self.as_raw_mut(), bound.into()) as u32 }
    }
}

/**
Custom random number generator to be used with [`RandState`].

The methods implemented for this trait, as well as possible
destructors, can be used by FFI callback functions. If these methods
panic, they can cause the program to abort.

# Examples

```rust
use rug::{rand::RandGen, Integer};
struct SimpleGenerator {
    seed: u64,
}
impl RandGen for SimpleGenerator {
    fn gen(&mut self) -> u32 {
        self.seed =
            self.seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (self.seed >> 32) as u32
    }
    fn seed(&mut self, seed: &Integer) {
        self.seed = seed.to_u64_wrapping();
    }
}
let mut rand = SimpleGenerator { seed: 1 };
assert_eq!(rand.gen(), 1481765933);
assert_eq!(rand.seed, 6364136223846793006);
```

[`RandState`]: struct.RandState.html
*/
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

    /// Gets up to 32 random bits.
    ///
    /// The default implementation simply calls the [`gen`] method
    /// once and returns the most significant required bits.
    ///
    /// This method can be overridden to store any unused bits for
    /// later use. This can be useful for example if the random number
    /// generation process is computationally expensive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandGen;
    /// struct SimpleGenerator {
    ///     seed: u64,
    ///     buffer: u64,
    ///     len: u32,
    /// }
    /// impl RandGen for SimpleGenerator {
    ///     fn gen(&mut self) -> u32 {
    ///         self.gen_bits(32)
    ///     }
    ///     fn gen_bits(&mut self, bits: u32) -> u32 {
    ///         let mut bits = match bits {
    ///             0 => return 0,
    ///             1..=31 => bits,
    ///             _ => 32,
    ///         };
    ///         let mut ret = 0;
    ///         if bits > self.len {
    ///             bits -= self.len;
    ///             ret |= (self.buffer << bits) as u32;
    ///             self.seed = self.seed.wrapping_mul(6364136223846793005);
    ///             self.seed = self.seed.wrapping_add(1);
    ///             self.buffer = self.seed;
    ///             self.len = 64;
    ///         }
    ///         self.len -= bits;
    ///         ret |= (self.buffer >> self.len) as u32;
    ///         self.buffer &= !(!0 << self.len);
    ///         ret
    ///     }
    /// }
    /// let mut rand = SimpleGenerator {
    ///     seed: 1,
    ///     buffer: 0,
    ///     len: 0,
    /// };
    /// let full = 6364136223846793006_u64;
    /// assert_eq!(rand.gen_bits(16), (full >> 48) as u32);
    /// assert_eq!(rand.gen_bits(32), (full >> 16) as u32);
    /// assert_eq!(rand.gen_bits(16), full as u32 & 0xffff);
    /// ```
    ///
    /// [`gen`]: #tymethod.gen
    fn gen_bits(&mut self, bits: u32) -> u32 {
        let gen = self.gen();
        match bits {
            0 => 0,
            1..=32 => gen >> (32 - bits),
            _ => gen,
        }
    }

    /// Seeds the random number generator.
    ///
    /// The default implementation of this function does nothing.
    ///
    /// Note that the [`RandState::seed`] method will pass its seed
    /// parameter exactly to this function without using it otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{RandGen, RandState},
    ///     Assign, Integer,
    /// };
    /// struct Seed {
    ///     inner: Integer,
    /// };
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         self.inner.to_u32_wrapping()
    ///     }
    ///     fn seed(&mut self, seed: &Integer) {
    ///         self.inner.assign(seed);
    ///     }
    /// }
    /// let mut seed = Seed {
    ///     inner: Integer::from(12),
    /// };
    /// let i = Integer::from(12345);
    /// {
    ///     let mut rand = RandState::new_custom(&mut seed);
    ///     rand.seed(&i);
    /// }
    /// assert_eq!(seed.inner, i);
    /// ```
    ///
    /// Since the seed parameter is only passed to this function and
    /// not used otherwise, with unsafe code you can pass a reference
    /// to anything, or even an `isize` or `usize`, to the seeding
    /// function.
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{RandGen, RandState},
    ///     Integer,
    /// };
    /// use std::mem;
    /// struct Seed {
    ///     num: isize,
    /// };
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         0x8cef7310
    ///     }
    ///     fn seed(&mut self, seed: &Integer) {
    ///         // unsafe code to transmute from &Integer to isize
    ///         self.num = unsafe { mem::transmute(seed) };
    ///     }
    /// }
    /// let mut seed = Seed { num: 15 };
    /// let i = -12345_isize;
    /// {
    ///     // unsafe code to transmute from isize to &Integer
    ///     let ir = unsafe { mem::transmute(i) };
    ///     let mut rand = RandState::new_custom(&mut seed);
    ///     rand.seed(ir);
    /// }
    /// assert_eq!(seed.num, i);
    /// ```
    ///
    /// [`RandState::seed`]: struct.RandState.html#method.seed
    #[inline]
    fn seed(&mut self, seed: &Integer) {
        let _ = seed;
    }

    /// Optionally clones the random number generator.
    ///
    /// The default implementation returns [`None`].
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
    ///     fn boxed_clone(&self) -> Option<Box<dyn RandGen>> {
    ///         let other = SimpleGenerator { seed: self.seed };
    ///         let boxed = Box::new(other);
    ///         Some(boxed)
    ///     }
    /// }
    /// let mut rand = SimpleGenerator { seed: 1 };
    /// let first = rand.gen();
    /// assert_eq!(rand.seed, 6364136223846793006);
    /// assert_eq!(first, 1481765933);
    /// let mut other = rand.boxed_clone().unwrap();
    /// let second = rand.gen();
    /// assert_eq!(rand.seed, 13885033948157127959);
    /// assert_eq!(second, 3232861391);
    /// let second_other = other.gen();
    /// assert_eq!(second_other, 3232861391);
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/std/option/enum.Option.html#variant.None
    #[inline]
    fn boxed_clone(&self) -> Option<Box<dyn RandGen>> {
        None
    }
}

fn _static_assertions() {
    static_assert_size!(RandState<'_>, randstate_t);
}

#[repr(C)]
struct Funcs {
    seed: Option<unsafe extern "C" fn(*mut randstate_t, *const gmp::mpz_t)>,
    get: Option<unsafe extern "C" fn(*mut randstate_t, *mut gmp::limb_t, c_ulong)>,
    clear: Option<unsafe extern "C" fn(*mut randstate_t)>,
    iset: Option<unsafe extern "C" fn(*mut randstate_t, *const randstate_t)>,
}

#[cfg(not(ffi_panic_aborts))]
macro_rules! c_callback {
    ($(fn $func:ident($($param:tt)*) $body:block)*) => { $(
        unsafe extern "C" fn $func($($param)*) {
            panic::catch_unwind(AssertUnwindSafe(|| $body))
                .unwrap_or_else(|_| process::abort())
        }
    )* };
}

#[cfg(ffi_panic_aborts)]
macro_rules! c_callback {
    ($(fn $func:ident($($param:tt)*) $body:block)*) => { $(
        unsafe extern "C" fn $func($($param)*) $body
    )* };
}

c_callback! {
    fn abort_seed(_: *mut randstate_t, _: *const gmp::mpz_t) {
        process::abort();
    }

    fn abort_get(_: *mut randstate_t, _: *mut gmp::limb_t, _: c_ulong) {
        process::abort();
    }

    fn abort_clear(_: *mut randstate_t) {
        process::abort();
    }

    fn abort_iset(_: *mut randstate_t, _: *const randstate_t) {
        process::abort();
    }

    fn custom_seed(s: *mut randstate_t, seed: *const gmp::mpz_t) {
        let r_ptr = (*s).seed.d as *mut &mut dyn RandGen;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn custom_get(s: *mut randstate_t, limb: *mut gmp::limb_t, bits: c_ulong) {
        let r_ptr = (*s).seed.d as *mut &mut dyn RandGen;
        gen_bits(*r_ptr, limb, bits);
    }

    fn custom_clear(s: *mut randstate_t) {
        let r_ptr = (*s).seed.d as *mut &mut dyn RandGen;
        drop(Box::from_raw(r_ptr));
    }

    fn custom_iset(dst: *mut randstate_t, src: *const randstate_t) {
        let r_ptr = (*src).seed.d as *const &mut dyn RandGen;
        gen_copy(*r_ptr, dst);
    }

    fn custom_boxed_seed(s: *mut randstate_t, seed: *const gmp::mpz_t) {
        let r_ptr = (*s).seed.d as *mut Box<dyn RandGen>;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn custom_boxed_get(
        s: *mut randstate_t,
        limb: *mut gmp::limb_t,
        bits: c_ulong,
    ) {
        let r_ptr = (*s).seed.d as *mut Box<dyn RandGen>;
        gen_bits(&mut **r_ptr, limb, bits);
    }

    fn custom_boxed_clear(s: *mut randstate_t) {
        let r_ptr = (*s).seed.d as *mut Box<dyn RandGen>;
        drop(Box::from_raw(r_ptr));
    }

    fn custom_boxed_iset(dst: *mut randstate_t, src: *const randstate_t) {
        let r_ptr = (*src).seed.d as *const Box<dyn RandGen>;
        gen_copy(&**r_ptr, dst);
    }
}

#[cfg(gmp_limb_bits_64)]
unsafe fn gen_bits(gen: &mut dyn RandGen, limb: *mut gmp::limb_t, bits: c_ulong) {
    let (limbs, rest) = (bits / 64, bits % 64);
    let limbs: isize = cast::cast(limbs);
    for i in 0..limbs {
        let n = u64::from(gen.gen()) | u64::from(gen.gen()) << 32;
        *limb.offset(i) = cast::cast(n);
    }
    if rest >= 32 {
        let mut n = u64::from(gen.gen());
        if rest > 32 {
            let mask = !(!0 << (rest - 32));
            n |= u64::from(gen.gen_bits(cast::cast(rest - 32)) & mask) << 32;
        }
        *limb.offset(limbs) = cast::cast(n);
    } else if rest > 0 {
        let mask = !(!0 << rest);
        let n = u64::from(gen.gen_bits(cast::cast(rest)) & mask);
        *limb.offset(limbs) = cast::cast(n);
    }
}

#[cfg(gmp_limb_bits_32)]
unsafe fn gen_bits(gen: &mut dyn RandGen, limb: *mut gmp::limb_t, bits: c_ulong) {
    let (limbs, rest) = (bits / 32, bits % 32);
    let limbs: isize = cast::cast(limbs);
    for i in 0..limbs {
        *limb.offset(i) = cast::cast(gen.gen());
    }
    if rest > 0 {
        let mask = !(!0 << rest);
        *limb.offset(limbs) = cast::cast(gen.gen_bits(cast::cast(rest)) & mask);
    }
}

unsafe fn gen_copy(gen: &dyn RandGen, dst: *mut randstate_t) {
    let other = gen.boxed_clone();
    // Do not panic here if other is None, as panics cannot cross FFI
    // boundareies. Instead, set dst_ptr.seed.d to null.
    let (dst_r_ptr, funcs) = if let Some(other) = other {
        let b: Box<Box<dyn RandGen>> = Box::new(other);
        let dst_r_ptr: *mut Box<dyn RandGen> = Box::into_raw(b);
        let funcs = &CUSTOM_BOXED_FUNCS as *const Funcs as *mut c_void;
        (dst_r_ptr, funcs)
    } else {
        (ptr::null_mut(), &ABORT_FUNCS as *const Funcs as *mut c_void)
    };
    *dst = randstate_t {
        seed: gmp::mpz_t {
            alloc: 0,
            size: 0,
            d: dst_r_ptr as *mut gmp::limb_t,
        },
        alg: 0,
        algdata: funcs,
    };
}

const ABORT_FUNCS: Funcs = Funcs {
    seed: Some(abort_seed),
    get: Some(abort_get),
    clear: Some(abort_clear),
    iset: Some(abort_iset),
};

const CUSTOM_FUNCS: Funcs = Funcs {
    seed: Some(custom_seed),
    get: Some(custom_get),
    clear: Some(custom_clear),
    iset: Some(custom_iset),
};

const CUSTOM_BOXED_FUNCS: Funcs = Funcs {
    seed: Some(custom_boxed_seed),
    get: Some(custom_boxed_get),
    clear: Some(custom_boxed_clear),
    iset: Some(custom_boxed_iset),
};

#[cfg(test)]
mod tests {
    use crate::rand::{RandGen, RandState};

    struct SimpleGenerator {
        seed: u64,
    }

    impl RandGen for SimpleGenerator {
        fn gen(&mut self) -> u32 {
            self.seed = self
                .seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (self.seed >> 32) as u32
        }
        fn boxed_clone(&self) -> Option<Box<dyn RandGen>> {
            let other = SimpleGenerator { seed: self.seed };
            let boxed = Box::new(other);
            Some(boxed)
        }
    }

    #[test]
    fn check_custom_clone() {
        let mut gen = SimpleGenerator { seed: 1 };
        let third2;
        {
            let mut rand1 = RandState::new_custom(&mut gen);
            let mut rand2 = rand1.clone();
            let first1 = rand1.bits(32);
            let first2 = rand2.bits(32);
            assert_eq!(first1, first2);
            let second1 = rand1.bits(32);
            let second2 = rand2.bits(32);
            assert_eq!(second1, second2);
            assert_ne!(first1, second1);
            third2 = rand2.bits(32);
            assert_ne!(second2, third2);
        }
        let mut rand3 = RandState::new_custom_boxed(Box::new(gen));
        let mut rand4 = rand3.clone();
        let third3 = rand3.bits(32);
        let third4 = rand4.bits(32);
        assert_eq!(third2, third3);
        assert_eq!(third2, third4);
    }

    struct NoCloneGenerator;

    impl RandGen for NoCloneGenerator {
        fn gen(&mut self) -> u32 {
            0
        }
    }

    #[test]
    #[should_panic(expected = "`RandGen::boxed_clone` returned `None`")]
    fn check_custom_no_clone() {
        let mut gen = NoCloneGenerator;
        let rand1 = RandState::new_custom(&mut gen);
        let _ = rand1.clone();
    }
}
