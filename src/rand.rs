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

//! TODO: document mod `rand`

use gmp_mpfr_sys::gmp::{self, randstate_t};
use inner::{Inner, InnerMut};
use integer::Integer;
use std::marker::PhantomData;
use std::mem;
use std::os::raw::{c_int, c_ulong, c_void};

/// The state of a random number generator.
pub struct RandState<'a> {
    inner: randstate_t,
    phantom: PhantomData<&'a RandGen>,
}

impl<'a> Default for RandState<'a> {
    fn default() -> RandState<'a> {
        RandState::new()
    }
}

impl<'a> Clone for RandState<'a> {
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
    fn drop(&mut self) {
        unsafe {
            self.inner_mut();
            gmp::randclear(self.inner_mut());
        }
    }
}

/// Generates a random number.
pub trait RandGen {
    /// Gets a random 32-bit unsigned integer.
    fn gen(&mut self) -> u32;
}

impl<'a> RandState<'a> {
    /// Creates a new random generator with a compromise between speed
    /// and randomness.
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
    /// algorithm *X* = (*a* × *X* + *c) mod 2<sup>*bits*</sup>.
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
    /// algorithm like
    /// [`new_linear_congruential()`](#method.new_linear_congruential).
    ///
    /// *a*, *c* and *bits* are selected from a table such that *size*
    /// bits of each *X* will be used, that is 2<sup>*bits*</sup> ≥
    /// *size*.
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
    /// A `RandState` state created with this function cannot be cloned;
    /// an attempted clone will result in a panic.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::{RandGen, RandState};
    /// struct Seed;
    /// impl RandGen for Seed {
    ///     fn gen(&mut self) -> u32 { 0xffff }
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
        let b = Box::<&mut RandGen>::new(custom);
        let inner = MpRandState {
            seed: Mpz {
                _alloc: 0,
                _size: 0,
                d: Box::into_raw(b) as *mut gmp::limb_t,
            },
            _alg: RandAlg::_DEFAULT,
            _algdata: &FUNCS as *const _ as *mut _,
        };
        RandState {
            inner: unsafe { mem::transmute(inner) },
            phantom: PhantomData,
        }
    }
}

#[repr(C)]
struct Mpz {
    _alloc: c_int,
    _size: c_int,
    d: *mut gmp::limb_t,
}

#[repr(C)]
enum RandAlg {
    _DEFAULT = 0,
}

#[repr(C)]
struct MpRandState {
    seed: Mpz,
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

unsafe extern "C" fn gen_seed(_s: *mut randstate_t, _seed: *const gmp::mpz_t) {
    unreachable!();
}

unsafe extern "C" fn gen_get(
    s: *mut randstate_t,
    limb: *mut gmp::limb_t,
    bits: c_ulong,
) {
    let s_ptr = s as *mut MpRandState;
    let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
    match gmp::LIMB_BITS {
        64 => {}
        32 => {}
        _ => unreachable!(),
    }
    // TODO: placeholder
    if bits > 0 {
        *limb = ((*r_ptr).gen() & !(!0 << bits)) as gmp::limb_t;
    }
}

unsafe extern "C" fn gen_clear(s: *mut randstate_t) {
    let s_ptr = s as *mut MpRandState;
    let r_ptr = (*s_ptr).seed.d as *mut &mut RandGen;
    drop(Box::from_raw(*r_ptr));
}

unsafe extern "C" fn gen_iset(_s: *mut randstate_t, _src: *const randstate_t) {
    panic!("cannot clone custom Rand");
}

const FUNCS: Funcs = Funcs {
    _seed: Some(gen_seed),
    _get: Some(gen_get),
    _clear: Some(gen_clear),
    _iset: Some(gen_iset),
};

impl<'a> Inner for RandState<'a> {
    type Output = randstate_t;
    fn inner(&self) -> &randstate_t {
        &self.inner
    }
}

impl<'a> InnerMut for RandState<'a> {
    unsafe fn inner_mut(&mut self) -> &mut randstate_t {
        &mut self.inner
    }
}
