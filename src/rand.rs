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

//! `rand` module.

use Integer;
use gmp_mpfr_sys::gmp::{self, randstate_t};
use inner::{Inner, InnerMut};
use std::marker::PhantomData;
use std::mem;
use std::os::raw::{c_int, c_ulong};
use std::sync::atomic::{AtomicPtr, Ordering};

/// Generates a random number.
pub trait RandGen {
    /// Gets a random 32-bit unsigned integer.
    fn gen(&mut self) -> u32;
}

enum RandomInner<'a> {
    Gmp(randstate_t),
    Custom(&'a mut InnerMut<Output = randstate_t>),
}

impl<'a> Drop for RandomInner<'a> {
    fn drop(&mut self) {
        match *self {
            RandomInner::Gmp(ref mut r) => unsafe { gmp::randclear(r) },
            RandomInner::Custom(_) => {}
        }
    }
}

/// The state of a random number generator.
pub struct Random<'a> {
    inner: RandomInner<'a>,
}

impl<'a> Random<'a> {
    /// Creates a new random generator with a compromise between speed
    /// and randomness.
    pub fn new() -> Random<'a> {
        unsafe {
            let mut r: randstate_t = mem::uninitialized();
            gmp::randinit_default(&mut r);
            Random { inner: RandomInner::Gmp(r) }
        }
    }

    /// Creates a random generator with a Mersenne Twister algorithm.
    pub fn new_mersenne_twister() -> Random<'a> {
        unsafe {
            let mut r: randstate_t = mem::uninitialized();
            gmp::randinit_mt(&mut r);
            Random { inner: RandomInner::Gmp(r) }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm *X* = (*a* × *X* + *c) mod 2<sup>*bits*</sup>.
    pub fn new_linear_congruential(
        a: &Integer,
        c: u32,
        bits: u32,
    ) -> Random<'a> {
        unsafe {
            let mut r: randstate_t = mem::uninitialized();
            gmp::randinit_lc_2exp(&mut r, a.inner(), c.into(), bits.into());
            Random { inner: RandomInner::Gmp(r) }
        }
    }

    /// Creates a new random generator with a linear congruential
    /// algorithm like
    /// [`new_linear_congruential()`](#method.new_linear_congruential).
    ///
    /// *a*, *c* and *bits* are selected from a table such that *size*
    /// bits of each *X* will be used, that is 2<sup>*bits*</sup> ≥
    /// *size*.
    pub fn new_linear_congruential_size(size: u32) -> Option<Random<'a>> {
        unsafe {
            let mut r: randstate_t = mem::uninitialized();
            if gmp::randinit_lc_2exp_size(&mut r, size.into()) != 0 {
                Some(Random { inner: RandomInner::Gmp(r) })
            } else {
                None
            }
        }
    }

    /// Creates a new custom random generator.
    pub fn new_custom<'c, T: 'c + RandGen>(
        c: &'c mut CustomRandom<'c, T>,
    ) -> Random<'c> {
        Random { inner: RandomInner::Custom(c) }
    }
}

impl<'a> Default for Random<'a> {
    fn default() -> Random<'a> {
        Random::new()
    }
}

impl<'a> Inner for Random<'a> {
    type Output = randstate_t;
    fn inner(&self) -> &randstate_t {
        match self.inner {
            RandomInner::Gmp(ref r) => r,
            RandomInner::Custom(ref r) => r.inner(),
        }
    }
}

impl<'a> InnerMut for Random<'a> {
    unsafe fn inner_mut(&mut self) -> &mut randstate_t {
        match self.inner {
            RandomInner::Gmp(ref mut r) => r,
            RandomInner::Custom(ref mut r) => r.inner_mut(),
        }
    }
}

#[repr(C)]
struct LikeMpz<T> {
    _alloc: c_int,
    _size: c_int,
    d: *mut T,
}

#[repr(C)]
enum LikeRandAlg {
    _DEFAULT = 0,
}

#[repr(C)]
struct LikeRandState<T> {
    seed: LikeMpz<T>,
    _alg: LikeRandAlg,
    funcs_ptr: AtomicPtr<Funcs>,
}

/// Custom `Random` generator.
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::rand::{CustomRandom, RandGen, Random};
/// struct Seed;
/// impl RandGen for Seed {
///     fn gen(&mut self) -> u32 { 0xffff }
/// }
/// let mut seed = Seed;
/// let mut custom = CustomRandom::new(&mut seed);
/// let mut rand = Random::new_custom(&mut custom);
/// let mut i = Integer::from(15);
/// i.random_below(&mut rand);
/// println!("0 <= {} < 15", i);
/// assert!(i < 15);
/// ```
pub struct CustomRandom<'a, T: 'a + RandGen> {
    state: LikeRandState<T>,
    funcs: Funcs,
    phantom: PhantomData<&'a T>,
}

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

impl<'a, T: 'a + RandGen> CustomRandom<'a, T> {
    /// Creates a new `CustomRandom`.
    pub fn new(t: &'a mut T) -> CustomRandom<'a, T> {
        CustomRandom {
            state: LikeRandState {
                seed: LikeMpz {
                    _alloc: 0,
                    _size: 0,
                    d: t as *mut _ as *mut _,
                },
                _alg: LikeRandAlg::_DEFAULT,
                funcs_ptr: Default::default(),
            },
            funcs: Funcs {
                _seed: None,
                _get: Some(CustomRandom::<'a, T>::get_randstate),
                _clear: None,
                _iset: None,
            },
            phantom: PhantomData,
        }
    }

    /// Gets a `Random` borrowing this `CustomRandom`.
    pub fn random(&mut self) -> Random {
        Random { inner: RandomInner::Custom(self) }
    }

    fn update_funcs_ptr(&self) {
        // sanity check
        assert_eq!(
            mem::size_of::<LikeRandState<T>>(),
            mem::size_of::<randstate_t>()
        );
        // Since this is borrowed, funcs won't move around, and we can
        // set the funcs_ptr field.
        let ptr = &self.funcs as *const _ as *mut _;
        self.state.funcs_ptr.store(ptr, Ordering::Relaxed);
    }

    unsafe extern "C" fn get_randstate(
        r: *mut randstate_t,
        limb: *mut gmp::limb_t,
        bits: c_ulong,
    ) {
        let randstate_ptr = r as *mut LikeRandState<T>;
        let random_ptr = (*randstate_ptr).seed.d;
        let random = &mut *random_ptr;
        // TODO: placeholder
        println!("bits: {}", bits);
        if bits > 0 {
            *limb = (random.gen() & !(!0 << bits)) as gmp::limb_t;
        }
    }
}

impl<'a, T: 'a + RandGen> Inner for CustomRandom<'a, T> {
    type Output = randstate_t;
    fn inner(&self) -> &randstate_t {
        self.update_funcs_ptr();
        let ptr = &self.state as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<'a, T: 'a + RandGen> InnerMut for CustomRandom<'a, T> {
    unsafe fn inner_mut(&mut self) -> &mut randstate_t {
        self.update_funcs_ptr();
        let ptr = &mut self.state as *mut _ as *mut _;
        &mut *ptr
    }
}
