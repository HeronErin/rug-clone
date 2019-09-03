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
//
// The proper fix will be to use MaybeUninit when gmp-mpfr-sys 1.2 is
// eventually released.

use crate::{cast, Integer};
use gmp_mpfr_sys::gmp::{self, limb_t, mpz_t, randstate_t};
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
#[derive(Debug)]
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
    /// Currently this is equivalent to [`new_mersenne_twister`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    ///
    /// [`new_mersenne_twister`]: #method.new_mersenne_twister
    #[inline]
    pub fn new() -> RandState<'static> {
        RandState::new_mersenne_twister()
    }

    /// Creates a random generator with a Mersenne Twister algorithm.
    ///
    /// This algorithm is fast and has good randomness properties.
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
    /// algorithm <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>) mod 2<sup><i>m</i></sup>.
    ///
    /// The low bits of <i>X</i> in this algorithm are not very
    /// random, so only the high half of each <i>X</i> is actually
    /// used, that is the higher <i>m</i>/2 bits.
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
    /// let m = 100;
    /// let mut rand = RandState::new_linear_congruential(&a, c, m);
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    pub fn new_linear_congruential(a: &Integer, c: u32, m: u32) -> RandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner, inner_ptr);
            gmp::randinit_lc_2exp(inner_ptr, a.as_raw(), c.into(), m.into());
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
    /// For the linear congruential algorithm
    /// <i>X</i> = (<i>a</i> × <i>X</i> + <i>c</i>) mod 2<sup><i>m</i></sup>,
    /// <i>a</i>, <i>c</i> and <i>m</i> are selected from a table
    /// such that at least <i>size</i> bits of each <i>X</i> will be
    /// used, that is <i>m</i>/2 ≥ <i>size</i>. The table only has
    /// values for <i>size</i> ≤ 128; [`None`] will be returned if the
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
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
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
    ///         // not really random
    ///         0x8CEF_7310
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
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`RandGen::boxed_clone`]: trait.RandGen.html#method.boxed_clone
    pub fn new_custom(custom: &mut dyn RandGen) -> RandState<'_> {
        let b: Box<&mut dyn RandGen> = Box::new(custom);
        let r_ptr: *mut &mut dyn RandGen = Box::into_raw(b);
        let inner = randstate_t {
            seed: mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut limb_t,
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
    ///         // not really random
    ///         0x8CEF_7310
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
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`RandGen::boxed_clone`]: trait.RandGen.html#method.boxed_clone
    pub fn new_custom_boxed(custom: Box<dyn RandGen>) -> RandState<'static> {
        let b: Box<Box<dyn RandGen>> = Box::new(custom);
        let r_ptr: *mut Box<dyn RandGen> = Box::into_raw(b);
        let inner = randstate_t {
            seed: mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut limb_t,
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
    ///     do not initialize all fields of the [`randstate_t`]
    ///     object, which can eventually lead to reading uninitialized
    ///     memory, and that is undefined behaviour in Rust even if no
    ///     decision is made using the read value. One way to ensure
    ///     that there is no uninitialized memory inside `raw` is to
    ///     use [`MaybeUninit::zeroed`] to initialize `raw` before
    ///     initializing with a function such as [`randinit_default`],
    ///     like in the example below.
    ///   * The [`randstate_t`] type can be considered as a kind of
    ///     pointer, so there can be multiple copies of it. Since this
    ///     function takes over ownership, no other copies of the
    ///     passed value should exist.
    ///   * The object must be thread safe.
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
    /// [`MaybeUninit::zeroed`]: https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#method.zeroed
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
    /// # Panics
    ///
    /// This method panics if the [`RandState`] object was created
    /// using [`new_custom`], as the borrow into the custom generator
    /// would be terminated once `self` is consumed. This would lead
    /// to undefined behavior if the returned object is used. This
    /// method does work with objects created using
    /// [`new_custom_boxed`].
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
    /// [`RandState`]: struct.RandState.html
    /// [`new_custom_boxed`]: #method.new_custom_boxed
    /// [`new_custom`]: #method.new_custom
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn into_raw(self) -> randstate_t {
        let ret = self.inner;
        let funcs = ret.algdata as *const Funcs;
        assert!(
            !ptr::eq(funcs, &CUSTOM_FUNCS) && !ptr::eq(funcs, &THREAD_CUSTOM_FUNCS),
            "cannot convert custom `RandState` into raw, \
             consider using `new_custom_boxed` instead of `new_custom`"
        );
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

    /// Converts a random generator into
    /// <code>[Box][`Box`]&lt;dyn [RandGen][`RandGen`]&gt;</code>
    /// if possible.
    ///
    /// If the conversion is not possible,
    /// <code>[Err][`Err`](self)</code> is returned.
    ///
    /// This conversion is always possible when the random generator
    /// was created with [`new_custom_boxed`]. It is also possible if
    /// the generator was cloned, directly or indirectly, from another
    /// generator that was created with [`new_custom`] or
    /// [`new_custom_boxed`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::{RandGen, RandState};
    /// struct Seed;
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         // not really random
    ///         0x8CEF_7310
    ///     }
    /// }
    /// let seed = Box::new(Seed);
    /// let rand = RandState::new_custom_boxed(seed);
    /// let mut back_to_seed = rand.into_custom_boxed().unwrap();
    /// assert_eq!(back_to_seed.gen(), 0x8CEF_7310);
    /// ```
    ///
    /// [`Box`]: https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html
    /// [`Err`]: https://doc.rust-lang.org/nightly/core/result/enum.Result.html#variant.Err
    /// [`RandGen`]: trait.RandGen.html
    /// [`RandState::into_custom_boxed`]: struct.RandState.html#method.into_custom_boxed
    /// [`new_custom_boxed`]: #method.new_custom_boxed
    /// [`new_custom`]: #method.new_custom
    #[inline]
    pub fn into_custom_boxed(self) -> Result<Box<dyn RandGen>, Self> {
        if !ptr::eq(self.inner.algdata as *const Funcs, &CUSTOM_BOXED_FUNCS) {
            return Err(self);
        }
        let r_ptr = self.inner.seed.d as *mut Box<dyn RandGen>;
        mem::forget(self);
        let boxed_box: Box<Box<dyn RandGen>> = unsafe { Box::from_raw(r_ptr) };
        Ok(*boxed_box)
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
The state of a random number generator that is suitable for a single thread only.

This is similar to [`RandState`] but can only be used in a single thread.

# Examples

```rust
use rug::rand::ThreadRandState;
# struct Gen { _dummy: *const i32, seed: u64 };
# impl rug::rand::ThreadRandGen for Gen {
#     fn gen(&mut self) -> u32 {
#         self.seed = self.seed.wrapping_mul(0x5851_F42D_4C95_7F2D).wrapping_add(1);
#         (self.seed >> 32) as u32
#     }
# }
# fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
let mut gen = create_generator();
let mut rand = ThreadRandState::new_custom(&mut gen);
let u = rand.bits(32);
println!("32 random bits: {:032b}", u);
```

[`RandState`]: struct.RandState.html
*/
#[derive(Debug)]
#[repr(transparent)]
pub struct ThreadRandState<'a> {
    inner: randstate_t,
    phantom: PhantomData<&'a dyn ThreadRandGen>,
}

impl Clone for ThreadRandState<'_> {
    #[inline]
    fn clone(&self) -> ThreadRandState<'static> {
        unsafe {
            let_zeroed_ptr!(inner: randstate_t, inner_ptr);
            gmp::randinit_set(inner_ptr, self.as_raw());
            // If d is null, then boxed_clone must have returned None.
            let inner = assume_init!(inner);
            if inner.seed.d.is_null() {
                panic!("`ThreadRandGen::boxed_clone` returned `None`");
            }
            ThreadRandState {
                inner,
                phantom: PhantomData,
            }
        }
    }
}

impl Drop for ThreadRandState<'_> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::randclear(self.as_raw_mut());
        }
    }
}

impl ThreadRandState<'_> {
    /// Creates a new custom random generator.
    ///
    /// This is similar to [`RandState::new_custom`]. The difference
    /// is that this method takes a [`ThreadRandGen`] that does not
    /// have to implement [`Send`] or [`Sync`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{ThreadRandGen, ThreadRandState},
    ///     Integer,
    /// };
    /// // dummy pointer field to ensure Seed is not Send and not Sync
    /// struct Seed(*const ());
    /// impl ThreadRandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         // not really random
    ///         0x8CEF_7310
    ///     }
    /// }
    /// let mut seed = Seed(&());
    /// let mut rand = ThreadRandState::new_custom(&mut seed);
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 ≤ {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// [`RandState::new_custom`]: struct.RandState.html#method.new_custom
    /// [`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
    /// [`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
    /// [`ThreadRandGen`]: trait.ThreadRandGen.html
    pub fn new_custom(custom: &mut dyn ThreadRandGen) -> ThreadRandState<'_> {
        let b: Box<&mut dyn ThreadRandGen> = Box::new(custom);
        let r_ptr: *mut &mut dyn ThreadRandGen = Box::into_raw(b);
        let inner = randstate_t {
            seed: mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut limb_t,
            },
            alg: 0,
            algdata: &THREAD_CUSTOM_FUNCS as *const Funcs as *mut c_void,
        };
        ThreadRandState {
            inner,
            phantom: PhantomData,
        }
    }

    /// Creates a new custom random generator.
    ///
    /// This is similar to [`RandState::new_custom_boxed`]. The
    /// difference is that this method takes a [`ThreadRandGen`] that
    /// does not have to implement [`Send`] or [`Sync`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{
    ///     rand::{ThreadRandGen, ThreadRandState},
    ///     Integer,
    /// };
    /// // dummy pointer field to ensure Seed is not Send and not Sync
    /// struct Seed(*const ());
    /// impl ThreadRandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         // not really random
    ///         0x8CEF_7310
    ///     }
    /// }
    /// let seed = Box::new(Seed(&()));
    /// let mut rand = ThreadRandState::new_custom_boxed(seed);
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 ≤ {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// [`RandState::new_custom_boxed`]: struct.RandState.html#method.new_custom_boxed
    /// [`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
    /// [`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
    /// [`ThreadRandGen`]: trait.ThreadRandGen.html
    pub fn new_custom_boxed(custom: Box<dyn ThreadRandGen>) -> ThreadRandState<'static> {
        let b: Box<Box<dyn ThreadRandGen>> = Box::new(custom);
        let r_ptr: *mut Box<dyn ThreadRandGen> = Box::into_raw(b);
        let inner = randstate_t {
            seed: mpz_t {
                alloc: 0,
                size: 0,
                d: r_ptr as *mut limb_t,
            },
            alg: 0,
            algdata: &THREAD_CUSTOM_BOXED_FUNCS as *const Funcs as *mut c_void,
        };
        ThreadRandState {
            inner,
            phantom: PhantomData,
        }
    }

    /// Creates a random generator from an initialized
    /// [GMP random generator][`randstate_t`].
    ///
    /// This is similar to [`RandState::from_raw`], but the object
    /// does not need to be thread safe. You *can* use this method if
    /// the object is thread safe, but in that case
    /// [`RandState::from_raw`] is probably better as it allows the
    /// returned object to be shared and transferred across threads.
    ///
    /// # Safety
    ///
    ///   * The value must be initialized. Note that the GMP functions
    ///     do not initialize all fields of the [`randstate_t`]
    ///     object, which can eventually lead to reading uninitialized
    ///     memory, and that is undefined behaviour in Rust even if no
    ///     decision is made using the read value. One way to ensure
    ///     that there is no uninitialized memory inside `raw` is to
    ///     use [`MaybeUninit::zeroed`] to initialize `raw` before
    ///     initializing with a function such as [`randinit_default`],
    ///     like in the example below.
    ///   * The [`randstate_t`] type can be considered as a kind of
    ///     pointer, so there can be multiple copies of it. Since this
    ///     function takes over ownership, no other copies of the
    ///     passed value should exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #![cfg_attr(nightly_maybe_uninit, feature(maybe_uninit))]
    /// # fn main() {
    /// # #[cfg(maybe_uninit)] {
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::ThreadRandState;
    /// use std::mem::MaybeUninit;
    /// let mut rand = unsafe {
    ///     // Do not use MabyeUninit::uninit, as gmp::randinit_default
    ///     // does not initialize all of the fields of raw.
    ///     let mut raw = MaybeUninit::zeroed();
    ///     gmp::randinit_default(raw.as_mut_ptr());
    ///     let raw = raw.assume_init();
    ///     // raw is initialized and unique
    ///     ThreadRandState::from_raw(raw)
    /// };
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// // since rand is a ThreadRandState now, deallocation is automatic
    /// # }
    /// # }
    /// ```
    ///
    /// [`MaybeUninit::zeroed`]: https://doc.rust-lang.org/nightly/core/mem/union.MaybeUninit.html#method.zeroed
    /// [`RandState::from_raw`]: struct.RandState.html#method.from_raw
    /// [`randinit_default`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/fn.randinit_default.html
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub unsafe fn from_raw(raw: randstate_t) -> ThreadRandState<'static> {
        ThreadRandState {
            inner: raw,
            phantom: PhantomData,
        }
    }

    /// Converts a random generator into a
    /// [GMP random generator][`randstate_t`].
    ///
    /// The returned object should be freed to avoid memory leaks.
    ///
    /// This is similar to [`RandState::into_raw`], but the returned
    /// object is not thread safe. Notably, it should *not* be used in
    /// [`RandState::from_raw`].
    ///
    /// # Panics
    ///
    /// This method panics if the [`ThreadRandState`] object was
    /// created using [`new_custom`], as the borrow into the custom
    /// generator would be terminated once `self` is consumed. This
    /// would lead to undefined behavior if the returned object is
    /// used. This method does work with objects created using
    /// [`new_custom_boxed`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::ThreadRandState;
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// # }
    /// # fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let gen = Box::new(create_generator());
    /// let rand = ThreadRandState::new_custom_boxed(gen);
    /// let mut raw = rand.into_raw();
    /// unsafe {
    ///     let u = gmp::urandomb_ui(&mut raw, 32) as u32;
    ///     println!("32 random bits: {:032b}", u);
    ///     // free object to prevent memory leak
    ///     gmp::randclear(&mut raw);
    /// }
    /// ```
    ///
    /// [`RandState::from_raw`]: struct.RandState.html#method.from_raw
    /// [`RandState::into_raw`]: struct.RandState.html#method.into_raw
    /// [`ThreadRandState`]: struct.ThreadRandState.html
    /// [`new_custom_boxed`]: #method.new_custom_boxed
    /// [`new_custom`]: #method.new_custom
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn into_raw(self) -> randstate_t {
        let ret = self.inner;
        let funcs = ret.algdata as *const Funcs;
        assert!(
            !ptr::eq(funcs, &CUSTOM_FUNCS) && !ptr::eq(funcs, &THREAD_CUSTOM_FUNCS),
            "cannot convert custom `ThreadRandState` into raw, \
             consider using `new_custom_boxed` instead of `new_custom`"
        );
        mem::forget(self);
        ret
    }

    /// Returns a pointer to the inner
    /// [GMP random generator][`randstate_t`].
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// This is similar to [`RandState::as_raw`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::ThreadRandState;
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// # }
    /// # fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let mut gen = create_generator();
    /// let mut rand = ThreadRandState::new_custom(&mut gen);
    /// let raw_ptr = rand.as_raw();
    /// // There is not much you can do with an immutable randstate_t pointer.
    /// println!("pointer: {:p}", raw_ptr);
    /// let u = rand.bits(32);
    /// println!("32 random bits: {:032b}", u);
    /// ```
    ///
    /// [`RandState::as_raw`]: struct.RandState.html#method.as_raw
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
    /// This is similar to [`RandState::as_raw_mut`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gmp_mpfr_sys::gmp;
    /// use rug::rand::ThreadRandState;
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// # }
    /// # fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let mut gen = create_generator();
    /// let mut rand = ThreadRandState::new_custom(&mut gen);
    /// let raw_ptr = rand.as_raw_mut();
    /// unsafe {
    ///     let u1 = gmp::urandomb_ui(raw_ptr, 32) as u32;
    ///     println!("32 random bits: {:032b}", u1);
    /// }
    /// let u2 = rand.bits(32);
    /// println!("another 32 random bits: {:032b}", u2);
    /// ```
    ///
    /// [`RandState::as_raw_mut`]: struct.RandState.html#method.as_raw_mut
    /// [`randstate_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.randstate_t.html
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut randstate_t {
        &mut self.inner
    }

    /// Converts a random generator into
    /// <code>[Box][`Box`]&lt;dyn [ThreadRandGen][`ThreadRandGen`]&gt;</code>
    /// if possible.
    ///
    /// If the conversion is not possible,
    /// <code>[Err][`Err`](self)</code> is returned.
    ///
    /// This conversion is always possible when the random generator
    /// was created with [`new_custom_boxed`]. It is also possible if
    /// the generator was cloned, directly or indirectly, from another
    /// generator that was created with [`new_custom`] or
    /// [`new_custom_boxed`].
    ///
    /// This is similar to [`RandState::into_custom_boxed`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::{ThreadRandGen, ThreadRandState};
    /// struct Seed;
    /// impl ThreadRandGen for Seed {
    ///     fn gen(&mut self) -> u32 {
    ///         // not really random
    ///         0x8CEF_7310
    ///     }
    /// }
    /// let seed = Box::new(Seed);
    /// let rand = ThreadRandState::new_custom_boxed(seed);
    /// let mut back_to_seed = rand.into_custom_boxed().unwrap();
    /// assert_eq!(back_to_seed.gen(), 0x8CEF_7310);
    /// ```
    ///
    /// [`Box`]: https://doc.rust-lang.org/nightly/alloc/boxed/struct.Box.html
    /// [`Err`]: https://doc.rust-lang.org/nightly/core/result/enum.Result.html#variant.Err
    /// [`RandState::into_custom_boxed`]: struct.RandState.html#method.into_custom_boxed
    /// [`ThreadRandGen`]: trait.ThreadRandGen.html
    /// [`new_custom_boxed`]: #method.new_custom_boxed
    /// [`new_custom`]: #method.new_custom
    #[inline]
    pub fn into_custom_boxed(self) -> Result<Box<dyn ThreadRandGen>, Self> {
        if !ptr::eq(
            self.inner.algdata as *const Funcs,
            &THREAD_CUSTOM_BOXED_FUNCS,
        ) {
            return Err(self);
        }
        let r_ptr = self.inner.seed.d as *mut Box<dyn ThreadRandGen>;
        mem::forget(self);
        let boxed_box: Box<Box<dyn ThreadRandGen>> = unsafe { Box::from_raw(r_ptr) };
        Ok(*boxed_box)
    }

    /// Seeds the random generator.
    ///
    /// This is similar to [`RandState::seed`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{rand::ThreadRandState, Integer};
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// #     fn seed(&mut self, seed: &Integer) { self.seed = seed.to_u64_wrapping() }
    /// # }
    /// # fn create_generator_with_seed() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let mut gen = create_generator_with_seed();
    /// let seed = Integer::from(123456);
    /// let mut rand = ThreadRandState::new_custom(&mut gen);
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
    ///
    /// [`RandState::seed`]: struct.RandState.html#method.seed
    #[inline]
    pub fn seed(&mut self, seed: &Integer) {
        unsafe {
            gmp::randseed(self.as_raw_mut(), seed.as_raw());
        }
    }

    /// Generates a random number with the specified number of bits.
    ///
    /// This is similar to [`RandState::bits`].
    ///
    /// # Panics
    ///
    /// Panics if `bits` is greater than 32.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::ThreadRandState;
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// # }
    /// # fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let mut gen = create_generator();
    /// let mut rand = ThreadRandState::new_custom(&mut gen);
    /// let u = rand.bits(16);
    /// assert!(u < (1 << 16));
    /// println!("16 random bits: {:016b}", u);
    /// ```
    ///
    /// [`RandState::bits`]: struct.RandState.html#method.bits
    #[inline]
    pub fn bits(&mut self, bits: u32) -> u32 {
        assert!(bits <= 32, "bits out of range");
        unsafe { gmp::urandomb_ui(self.as_raw_mut(), bits.into()) as u32 }
    }

    /// Generates a random number below the given boundary value.
    ///
    /// This is similar to [`RandState::below`].
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rand::ThreadRandState;
    /// # struct Gen { _dummy: *const i32, seed: u64 };
    /// # impl rug::rand::ThreadRandGen for Gen {
    /// #     fn gen(&mut self) -> u32 {
    /// #         self.seed = self.seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    /// #         (self.seed >> 32) as u32
    /// #     }
    /// # }
    /// # fn create_generator() -> Gen { Gen { _dummy: &0i32, seed: 1 } }
    /// let mut gen = create_generator();
    /// let mut rand = ThreadRandState::new_custom(&mut gen);
    /// let u = rand.below(10000);
    /// assert!(u < 10000);
    /// println!("0 ≤ {} < 10000", u);
    /// ```
    ///
    /// [`RandState::below`]: struct.RandState.html#method.below
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
use rug::{
    rand::{RandGen, RandState},
    Integer,
};
struct SimpleGenerator {
    seed: u64,
}
impl RandGen for SimpleGenerator {
    fn gen(&mut self) -> u32 {
        // linear congruential algorithm with m = 64
        const A: u64 = 0x5851_F42D_4C95_7F2D;
        const C: u64 = 1;
        self.seed = self.seed.wrapping_mul(A).wrapping_add(C);
        (self.seed >> 32) as u32
    }
    fn seed(&mut self, seed: &Integer) {
        self.seed = seed.to_u64_wrapping();
    }
}
let mut gen = SimpleGenerator { seed: 1 };
let mut state = RandState::new_custom(&mut gen);
assert_eq!(state.bits(32), 0x5851_F42D);
assert_eq!(state.bits(32), 0xC0B1_8CCF);
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
    ///         // linear congruential algorithm with m = 64
    ///         const A: u64 = 0x5851_F42D_4C95_7F2D;
    ///         const C: u64 = 1;
    ///         self.seed = self.seed.wrapping_mul(A).wrapping_add(C);
    ///         (self.seed >> 32) as u32
    ///     }
    /// }
    /// let mut rand = SimpleGenerator { seed: 1 };
    /// assert_eq!(rand.gen(), 0x5851_F42D);
    /// assert_eq!(rand.seed, 0x5851_F42D_4C95_7F2E);
    /// assert_eq!(rand.gen(), 0xC0B1_8CCF);
    /// assert_eq!(rand.seed, 0xC0B1_8CCF_4E25_2D17);
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
    ///     buffer: u32,
    ///     len: u32,
    /// }
    /// impl RandGen for SimpleGenerator {
    ///     fn gen(&mut self) -> u32 {
    ///         // linear congruential algorithm with m = 64
    ///         const A: u64 = 0x5851_F42D_4C95_7F2D;
    ///         const C: u64 = 1;
    ///         self.seed = self.seed.wrapping_mul(A).wrapping_add(C);
    ///         (self.seed >> 32) as u32
    ///     }
    ///     fn gen_bits(&mut self, bits: u32) -> u32 {
    ///         let mut bits = match bits {
    ///             0 => return 0,
    ///             1..=31 => bits,
    ///             _ => return self.gen(),
    ///         };
    ///         let mut ret = 0;
    ///         if bits > self.len {
    ///             bits -= self.len;
    ///             ret |= self.buffer << bits;
    ///             self.buffer = self.gen();
    ///             self.len = 32;
    ///         }
    ///         self.len -= bits;
    ///         ret |= self.buffer >> self.len;
    ///         self.buffer &= !(!0 << self.len);
    ///         ret
    ///     }
    /// }
    /// let mut rand = SimpleGenerator {
    ///     seed: 1,
    ///     buffer: 0,
    ///     len: 0,
    /// };
    /// let (first_32, second_32) = (0x5851_F42D, 0xC0B1_8CCF);
    /// assert_eq!(rand.gen_bits(24), first_32 >> 8);
    /// assert_eq!(rand.gen_bits(24), ((first_32 & 0xFF) << 16) | (second_32 >> 16));
    /// assert_eq!(rand.gen_bits(16), second_32 & 0xFFFF);
    /// ```
    ///
    /// [`gen`]: #tymethod.gen
    fn gen_bits(&mut self, bits: u32) -> u32 {
        let gen = self.gen();
        match bits {
            0 => 0,
            1..=31 => gen >> (32 - bits),
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
    ///         // linear congruential algorithm with m = 64
    ///         const A: u64 = 0x5851_F42D_4C95_7F2D;
    ///         const C: u64 = 1;
    ///         self.seed = self.seed.wrapping_mul(A).wrapping_add(C);
    ///         (self.seed >> 32) as u32
    ///     }
    ///     fn boxed_clone(&self) -> Option<Box<dyn RandGen>> {
    ///         let other = SimpleGenerator { seed: self.seed };
    ///         let boxed = Box::new(other);
    ///         Some(boxed)
    ///     }
    /// }
    /// let mut rand = SimpleGenerator { seed: 1 };
    /// assert_eq!(rand.gen(), 0x5851_F42D);
    /// assert_eq!(rand.seed, 0x5851_F42D_4C95_7F2E);
    /// let mut other = rand.boxed_clone().unwrap();
    /// assert_eq!(rand.gen(), 0xC0B1_8CCF);
    /// assert_eq!(rand.seed, 0xC0B1_8CCF_4E25_2D17);
    /// assert_eq!(other.gen(), 0xC0B1_8CCF);
    /// ```
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    #[inline]
    fn boxed_clone(&self) -> Option<Box<dyn RandGen>> {
        None
    }
}

/**
Custom random number generator to be used with [`ThreadRandState`].

The methods implemented for this trait, as well as possible
destructors, can be used by FFI callback functions. If these methods
panic, they can cause the program to abort.

This is similar to [`RandGen`] but can only be used in a single thread.

# Examples

```rust
# #[cfg(skip_this)]
use rand::{rngs::ThreadRng, thread_rng};
# struct ThreadRng(*const i32, u32);
# impl ThreadRng {
#     pub fn next_u32(&mut self) -> u32 { self.1 = self.1.wrapping_add(1); self.1 }
# }
# fn thread_rng() -> ThreadRng { ThreadRng(&0i32, !0 - 10) }
use rug::rand::{ThreadRandGen, ThreadRandState};
struct Generator(ThreadRng);
impl ThreadRandGen for Generator {
    fn gen(&mut self) -> u32 {
        self.0.next_u32()
    }
}
let mut rng = Generator(thread_rng());
let mut state = ThreadRandState::new_custom(&mut rng);
let u = state.below(10000);
assert!(u < 10000);
println!("0 ≤ {} < 10000", u);
```

This would not compile, since `ThreadRng` is not [`Send`] and not
[`Sync`].

```compile_fail
# #[cfg(skip_this)]
use rand::{rngs::ThreadRng, thread_rng};
# struct ThreadRng(*const i32, u32);
# impl ThreadRng {
#     pub fn next_u32(&mut self) -> u32 { self.1 = self.1.wrapping_add(1); self.1 }
# }
# fn thread_rng() -> ThreadRng { ThreadRng(&0i32, !0 - 10) }
use rug::rand::RandGen;
struct Generator(ThreadRng);
impl RandGen for Generator {
    fn gen(&mut self) -> u32 {
        self.0.next_u32()
    }
}
```

[`RandGen`]: trait.RandGen.html
[`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
[`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
[`ThreadRandState`]: struct.ThreadRandState.html
*/
pub trait ThreadRandGen {
    /// Gets a random 32-bit unsigned integer.
    ///
    /// This is similar to [`RandGen::gen`].
    ///
    /// [`RandGen::gen`]: trait.RandGen.html#tymethod.gen
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
    /// This method is similar to [`RandGen::gen_bits`].
    ///
    /// [`RandGen::gen_bits`]: trait.RandGen.html#method.gen_bits
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
    /// Note that the [`ThreadRandState::seed`] method will pass its seed
    /// parameter exactly to this function without using it otherwise.
    ///
    /// This method is similar to [`RandGen::seed`].
    ///
    /// [`RandGen::seed`]: trait.RandGen.html#method.seed
    /// [`ThreadRandState::seed`]: struct.ThreadRandState.html#method.seed
    #[inline]
    fn seed(&mut self, seed: &Integer) {
        let _ = seed;
    }

    /// Optionally clones the random number generator.
    ///
    /// The default implementation returns [`None`].
    ///
    /// This method is similar to [`RandGen::boxed_clone`].
    ///
    /// [`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
    /// [`RandGen::boxed_clone`]: trait.RandGen.html#method.boxed_clone
    #[inline]
    fn boxed_clone(&self) -> Option<Box<dyn ThreadRandGen>> {
        None
    }
}

fn _static_assertions() {
    static_assert_size!(RandState<'_>, randstate_t);
    static_assert_size!(ThreadRandState<'_>, randstate_t);
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct Funcs {
    seed: Option<unsafe extern "C" fn(rstate: *mut randstate_t, seed: *const mpz_t)>,
    get: Option<unsafe extern "C" fn(rstate: *mut randstate_t, dest: *mut limb_t, nbits: c_ulong)>,
    clear: Option<unsafe extern "C" fn(rstate: *mut randstate_t)>,
    iset: Option<unsafe extern "C" fn(dst: *mut randstate_t, src: *const randstate_t)>,
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

// abort functions do not need a wrapper to abort on panic, they never panic and always abort
unsafe extern "C" fn abort_seed(_: *mut randstate_t, _: *const mpz_t) {
    process::abort();
}

unsafe extern "C" fn abort_get(_: *mut randstate_t, _: *mut limb_t, _: c_ulong) {
    process::abort();
}

unsafe extern "C" fn abort_clear(_: *mut randstate_t) {
    process::abort();
}

unsafe extern "C" fn abort_iset(_: *mut randstate_t, _: *const randstate_t) {
    process::abort();
}

c_callback! {
    fn custom_seed(s: *mut randstate_t, seed: *const mpz_t) {
        let r_ptr = (*s).seed.d as *mut &mut dyn RandGen;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn custom_get(s: *mut randstate_t, limb: *mut limb_t, bits: c_ulong) {
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

    fn custom_boxed_seed(s: *mut randstate_t, seed: *const mpz_t) {
        let r_ptr = (*s).seed.d as *mut Box<dyn RandGen>;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn custom_boxed_get(
        s: *mut randstate_t,
        limb: *mut limb_t,
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

    fn thread_custom_seed(s: *mut randstate_t, seed: *const mpz_t) {
        let r_ptr = (*s).seed.d as *mut &mut dyn ThreadRandGen;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn thread_custom_get(s: *mut randstate_t, limb: *mut limb_t, bits: c_ulong) {
        let r_ptr = (*s).seed.d as *mut &mut dyn ThreadRandGen;
        thread_gen_bits(*r_ptr, limb, bits);
    }

    fn thread_custom_clear(s: *mut randstate_t) {
        let r_ptr = (*s).seed.d as *mut &mut dyn ThreadRandGen;
        drop(Box::from_raw(r_ptr));
    }

    fn thread_custom_iset(dst: *mut randstate_t, src: *const randstate_t) {
        let r_ptr = (*src).seed.d as *const &mut dyn ThreadRandGen;
        thread_gen_copy(*r_ptr, dst);
    }

    fn thread_custom_boxed_seed(s: *mut randstate_t, seed: *const mpz_t) {
        let r_ptr = (*s).seed.d as *mut Box<dyn ThreadRandGen>;
        (*r_ptr).seed(&*cast_ptr!(seed, Integer));
    }

    fn thread_custom_boxed_get(
        s: *mut randstate_t,
        limb: *mut limb_t,
        bits: c_ulong,
    ) {
        let r_ptr = (*s).seed.d as *mut Box<dyn ThreadRandGen>;
        thread_gen_bits(&mut **r_ptr, limb, bits);
    }

    fn thread_custom_boxed_clear(s: *mut randstate_t) {
        let r_ptr = (*s).seed.d as *mut Box<dyn ThreadRandGen>;
        drop(Box::from_raw(r_ptr));
    }

    fn thread_custom_boxed_iset(dst: *mut randstate_t, src: *const randstate_t) {
        let r_ptr = (*src).seed.d as *const Box<dyn ThreadRandGen>;
        thread_gen_copy(&**r_ptr, dst);
    }
}

#[cfg(gmp_limb_bits_64)]
unsafe fn gen_bits(gen: &mut dyn RandGen, limb: *mut limb_t, bits: c_ulong) {
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
unsafe fn gen_bits(gen: &mut dyn RandGen, limb: *mut limb_t, bits: c_ulong) {
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
    // Do not panic here if boxed_clone returns None, as panics cannot
    // cross FFI boundaries. Instead, set dst_ptr.seed.d to null.
    let (dst_r_ptr, funcs) = if let Some(other) = gen.boxed_clone() {
        let b: Box<Box<dyn RandGen>> = Box::new(other);
        let dst_r_ptr: *mut Box<dyn RandGen> = Box::into_raw(b);
        let funcs = &CUSTOM_BOXED_FUNCS as *const Funcs as *mut c_void;
        (dst_r_ptr, funcs)
    } else {
        (ptr::null_mut(), &ABORT_FUNCS as *const Funcs as *mut c_void)
    };
    *dst = randstate_t {
        seed: mpz_t {
            alloc: 0,
            size: 0,
            d: dst_r_ptr as *mut limb_t,
        },
        alg: 0,
        algdata: funcs,
    };
}

#[cfg(gmp_limb_bits_64)]
unsafe fn thread_gen_bits(gen: &mut dyn ThreadRandGen, limb: *mut limb_t, bits: c_ulong) {
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
unsafe fn thread_gen_bits(gen: &mut dyn ThreadRandGen, limb: *mut limb_t, bits: c_ulong) {
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

unsafe fn thread_gen_copy(gen: &dyn ThreadRandGen, dst: *mut randstate_t) {
    // Do not panic here if boxed_clone returns None, as panics cannot
    // cross FFI boundaries. Instead, set dst_ptr.seed.d to null.
    let (dst_r_ptr, funcs) = if let Some(other) = gen.boxed_clone() {
        let b: Box<Box<dyn ThreadRandGen>> = Box::new(other);
        let dst_r_ptr: *mut Box<dyn ThreadRandGen> = Box::into_raw(b);
        let funcs = &THREAD_CUSTOM_BOXED_FUNCS as *const Funcs as *mut c_void;
        (dst_r_ptr, funcs)
    } else {
        (ptr::null_mut(), &ABORT_FUNCS as *const Funcs as *mut c_void)
    };
    *dst = randstate_t {
        seed: mpz_t {
            alloc: 0,
            size: 0,
            d: dst_r_ptr as *mut limb_t,
        },
        alg: 0,
        algdata: funcs,
    };
}

static ABORT_FUNCS: Funcs = Funcs {
    seed: Some(abort_seed),
    get: Some(abort_get),
    clear: Some(abort_clear),
    iset: Some(abort_iset),
};

static CUSTOM_FUNCS: Funcs = Funcs {
    seed: Some(custom_seed),
    get: Some(custom_get),
    clear: Some(custom_clear),
    iset: Some(custom_iset),
};

static CUSTOM_BOXED_FUNCS: Funcs = Funcs {
    seed: Some(custom_boxed_seed),
    get: Some(custom_boxed_get),
    clear: Some(custom_boxed_clear),
    iset: Some(custom_boxed_iset),
};

static THREAD_CUSTOM_FUNCS: Funcs = Funcs {
    seed: Some(thread_custom_seed),
    get: Some(thread_custom_get),
    clear: Some(thread_custom_clear),
    iset: Some(thread_custom_iset),
};

static THREAD_CUSTOM_BOXED_FUNCS: Funcs = Funcs {
    seed: Some(thread_custom_boxed_seed),
    get: Some(thread_custom_boxed_get),
    clear: Some(thread_custom_boxed_clear),
    iset: Some(thread_custom_boxed_iset),
};

/// Used to generate random numbers.
///
/// This trait is implemented by
///   1. [`RandState`], which is thread safe and implements [`Send`]
///      and [`Sync`].
///   2. [`ThreadRandState`], which can only be used in a single
///      thread.
///
/// This trait is sealed and cannot be implemented for more types.
///
/// [`RandState`]: struct.RandState.html
/// [`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
/// [`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
/// [`ThreadRandState`]: struct.ThreadRandState.html
pub trait MutRandState: SealedMutRandState {}

mod hide {
    use gmp_mpfr_sys::gmp::randstate_t;
    #[repr(transparent)]
    pub struct Private<'a>(pub(crate) &'a mut randstate_t);
    pub trait SealedMutRandState {
        fn private(&mut self) -> Private;
    }
}
use self::hide::{Private, SealedMutRandState};

impl MutRandState for RandState<'_> {}
impl SealedMutRandState for RandState<'_> {
    #[inline]
    fn private(&mut self) -> Private {
        Private(&mut self.inner)
    }
}
impl MutRandState for ThreadRandState<'_> {}
impl SealedMutRandState for ThreadRandState<'_> {
    #[inline]
    fn private(&mut self) -> Private {
        Private(&mut self.inner)
    }
}

#[cfg(test)]
mod tests {
    use crate::rand::{RandGen, RandState, ThreadRandGen, ThreadRandState};
    use gmp_mpfr_sys::gmp;
    use std::ptr;

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

    #[test]
    #[should_panic(expected = "cannot convert custom `RandState` into raw")]
    fn check_custom_into_raw() {
        let mut gen = NoCloneGenerator;
        let rand1 = RandState::new_custom(&mut gen);
        let _ = rand1.into_raw();
    }

    // include a dummy pointer to make !Send and !Sync
    struct ThreadSimpleGenerator {
        _dummy: *const i32,
        seed: u64,
    }

    impl ThreadRandGen for ThreadSimpleGenerator {
        fn gen(&mut self) -> u32 {
            self.seed = self
                .seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (self.seed >> 32) as u32
        }
        fn boxed_clone(&self) -> Option<Box<dyn ThreadRandGen>> {
            let other = ThreadSimpleGenerator {
                _dummy: ptr::null(),
                seed: self.seed,
            };
            let boxed = Box::new(other);
            Some(boxed)
        }
    }

    #[test]
    fn thread_check_custom_clone() {
        let mut gen = ThreadSimpleGenerator {
            _dummy: ptr::null(),
            seed: 1,
        };
        let third2;
        {
            let mut rand1 = ThreadRandState::new_custom(&mut gen);
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
        let mut rand3 = ThreadRandState::new_custom_boxed(Box::new(gen));
        let mut rand4 = rand3.clone();
        let third3 = rand3.bits(32);
        let third4 = rand4.bits(32);
        assert_eq!(third2, third3);
        assert_eq!(third2, third4);
    }

    struct ThreadNoCloneGenerator;

    impl ThreadRandGen for ThreadNoCloneGenerator {
        fn gen(&mut self) -> u32 {
            0
        }
    }

    #[test]
    #[should_panic(expected = "`ThreadRandGen::boxed_clone` returned `None`")]
    fn thread_check_custom_no_clone() {
        let mut gen = ThreadNoCloneGenerator;
        let rand1 = ThreadRandState::new_custom(&mut gen);
        let _ = rand1.clone();
    }

    #[test]
    #[should_panic(expected = "cannot convert custom `ThreadRandState` into raw")]
    fn thread_check_custom_into_raw() {
        let mut gen = ThreadNoCloneGenerator;
        let rand1 = ThreadRandState::new_custom(&mut gen);
        let _ = rand1.into_raw();
    }

    #[test]
    fn thread_check_raw() {
        let mut check = RandState::new();
        // RandState is more restrictive than ThreadRandState; so this
        // conversion is sound.
        let mut state = unsafe { ThreadRandState::from_raw(check.clone().into_raw()) };
        assert_eq!(state.bits(32), check.bits(32));
        assert_eq!(
            unsafe { gmp::urandomb_ui(state.as_raw_mut(), 32) as u32 },
            check.bits(32)
        );
        let mut raw = state.into_raw();
        assert_eq!(
            unsafe { gmp::urandomb_ui(&mut raw, 32) as u32 },
            check.bits(32)
        );
        let mut state = unsafe { ThreadRandState::from_raw(raw) };
        assert_eq!(state.below(100), check.below(100));
    }

    #[test]
    fn congruential_size() {
        assert!(RandState::new_linear_congruential_size(128).is_some());
        assert!(RandState::new_linear_congruential_size(129).is_none());
    }
}
