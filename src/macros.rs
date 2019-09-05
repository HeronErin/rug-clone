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

#[cfg(feature = "integer")]
macro_rules! from_assign {
    ($Src:ty => $Dst:ty) => {
        impl From<$Src> for $Dst {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Dst as Assign<$Src>>::assign(&mut dst, src);
                dst
            }
        }
    };

    ($Src:ty => $Dst1:ty, $Dst2:ty) => {
        impl From<$Src> for ($Dst1, $Dst2) {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <(&mut $Dst1, &mut $Dst2) as Assign<$Src>>::assign(
                    &mut (&mut dst.0, &mut dst.1),
                    src,
                );
                dst
            }
        }
    };

    ($Src:ty => $Dst1:ty, $Dst2:ty, $Dst3:ty) => {
        impl From<$Src> for ($Dst1, $Dst2, $Dst3) {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <(&mut $Dst1, &mut $Dst2, &mut $Dst3) as Assign<$Src>>::assign(
                    &mut (&mut dst.0, &mut dst.1, &mut dst.2),
                    src,
                );
                dst
            }
        }
    };
}

// method(param*) -> Incomplete
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! math_op0 {
    (
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*) -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method($($param: $T),*) -> $Incomplete {
            $Incomplete {
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! ref_math_op0 {
    (
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete {
            $($param: $T,)*
        }

        impl Assign<$Incomplete> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete) {
                $func(self, $(src.$param),*);
            }
        }

        from_assign! { $Incomplete => $Big }
    };
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_ref(&self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op1 {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Self {
            self.$method_mut($($param),*);
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $($param: $T),*) {
            $func(self, None, $($param),*);
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! ref_math_op1 {
    (
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self, Some(src.ref_self), $(src.$param),*);
            }
        }

        from_assign! { $Incomplete<'_> => $Big }
    };
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op1_2 {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $rop: Self,
            $($param: $T,)*
        ) -> (Self, Self) {
            self.$method_mut(&mut $rop, $($param),*);
            (self, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $rop: &mut Self, $($param: $T),*) {
            $func(self, $rop, None, $($param),*);
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(
            &self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// (Big, Big) = Incomplete
// Incomplete -> (Big, Big)
#[cfg(feature = "integer")]
macro_rules! ref_math_op1_2 {
    (
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl Assign<$Incomplete<'_>> for (&mut $Big, &mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self.0, self.1, Some(src.ref_self), $(src.$param),*);
            }
        }

        impl Assign<$Incomplete<'_>> for ($Big, $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                <(&mut $Big, &mut $Big) as Assign<$Incomplete<'_>>>::assign(
                    &mut (&mut self.0, &mut self.1),
                    src,
                );
            }
        }

        from_assign! { $Incomplete<'_> => $Big, $Big }
    };
}

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_ref(&mut self, &Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2 {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &Self, $($param: $T),*) -> Self {
            self.$method_mut($op, $($param),*);
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &Self, $($param: $T),*) {
            $func(self, None, $op, $($param),*);
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! ref_math_op2 {
    (
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $op:ident $(, $param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self, Some(src.ref_self), src.$op, $(src.$param),*);
            }
        }

        from_assign! { $Incomplete<'_> => $Big }
    };
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self, &Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2_2 {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $op: Self,
            $($param: $T,)*
        ) -> (Self, Self) {
            self.$method_mut(&mut $op, $($param),*);
            (self, $op)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &mut Self, $($param: $T),*) {
            $func(self, $op, None, None, $($param),*);
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// (Big, Big) = Incomplete
// Incomplete -> (Big, Big)
#[cfg(feature = "integer")]
macro_rules! ref_math_op2_2 {
    (
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $op:ident $(, $param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl Assign<$Incomplete<'_>> for (&mut $Big, &mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(
                    self.0,
                    self.1,
                    Some(src.ref_self),
                    Some(src.$op),
                    $(src.$param,)*
                );
            }
        }

        impl Assign<$Incomplete<'_>> for ($Big, $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                <(&mut $Big, &mut $Big) as Assign<$Incomplete<'_>>>::assign(
                    &mut (&mut self.0, &mut self.1),
                    src,
                );
            }
        }

        from_assign! { $Incomplete<'_> => $Big, $Big }
    };
}

// method(self, Self, Self, param*) -> (Self, Self, Self)
// method_mut(&mut self, &mut Self, &mut Self, param*)
// method_mut(&mut self, &mut Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2_3 {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident, $rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $op: Self,
            mut $rop: Self,
            $($param: $T,)*
        ) -> (Self, Self, Self) {
            self.$method_mut(&mut $op, &mut $rop, $($param),*);
            (self, $op, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(
            &mut self,
            $op: &mut Self,
            $rop: &mut Self,
            $($param: $T,)*
        ) {
            $func(self, $op, Some($rop), None, None, $($param),*);
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    };
}

// #big -> Big
// big #=
// #&big -> Incomplete
// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! arith_unary {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $Incomplete:ident
    ) => {
        arith_unary! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $Incomplete;
            fn from_incomplete(src) {
                let mut dst = <Self as Default>::default();
                <$Big as Assign<$Incomplete<'_>>>::assign(&mut dst, src);
                dst
            }
        }
    };
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $Incomplete:ident;
        fn from_incomplete($from_src:ident) $from_block:block
    ) => {
        impl $Imp for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self) -> $Big {
                <$Big as $ImpAssign>::$method_assign(&mut self);
                self
            }
        }

        impl $ImpAssign for $Big {
            #[inline]
            fn $method_assign(&mut self) {
                $func(self, None);
            }
        }

        impl<'a> $Imp for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self) -> $Incomplete<'a> {
                $Incomplete { op: self }
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            op: &'a $Big,
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self, Some(src.op));
            }
        }

        impl From<$Incomplete<'_>> for $Big {
            #[inline]
            fn from($from_src: $Incomplete<'_>) -> $Big $from_block
        }
    };
}

// big # big -> Big
// big # &big -> Big
// &big # big -> Big
// &big # &big -> Incomplete
// big #= big
// big #= &big
// big #-> big
// &big #-> big
// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! arith_binary {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $Incomplete:ident;
        $rhs_has_more_alloc:path
    ) => {
        arith_binary! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpFrom { $method_from }
            $Incomplete;
            $rhs_has_more_alloc;
            fn from_incomplete(src) {
                let mut dst = <Self as Default>::default();
                <$Big as Assign<$Incomplete<'_>>>::assign(&mut dst, src);
                dst
            }
        }
    };
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $Incomplete:ident;
        $rhs_has_more_alloc:path;
        fn from_incomplete($from_src:ident) $from_block:block
    ) => {
        impl $Imp<$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, mut rhs: $Big) -> $Big {
                // use the allocation with the larger capacity
                if $rhs_has_more_alloc(&self, &rhs) {
                    rhs.$method_from(&self);
                    rhs
                } else {
                    self.$method_assign(&rhs);
                    self
                }
            }
        }

        impl $Imp<&$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &$Big) -> $Big {
                <$Big as $ImpAssign<&$Big>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl $Imp<$Big> for &$Big {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<&$Big>>::$method_from(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'_> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Big) {
                <$Big as $ImpAssign<&$Big>>::$method_assign(self, &rhs);
            }
        }

        impl $ImpAssign<&$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &$Big) {
                $func(self, None, Some(rhs));
            }
        }

        impl $ImpFrom<$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Big) {
                <$Big as $ImpFrom<&$Big>>::$method_from(self, &lhs);
            }
        }

        impl $ImpFrom<&$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$Big) {
                $func(self, Some(lhs), None);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: &'a $Big,
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self, Some(src.lhs), Some(src.rhs));
            }
        }

        impl From<$Incomplete<'_>> for $Big {
            #[inline]
            fn from($from_src: $Incomplete<'_>) -> $Big $from_block
        }
    };
}

// big # prim -> Big
// big # &prim -> Big
// &big # prim -> Incomplete
// &big # &prim -> Incomplete
// big #= prim
// big #= &prim
// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! arith_prim {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => { $(
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl $Imp<&$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &$T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, *rhs);
                self
            }
        }

        impl<'b> $Imp<$T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: $T) -> $Incomplete<'b> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl<'b> $Imp<&$T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$T) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                $func(self, None, rhs);
            }
        }

        impl $ImpAssign<&$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &$T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *rhs);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                $func(self, Some(src.lhs), src.rhs);
            }
        }

        from_assign! { $Incomplete<'_> => $Big }
    )* };
}

// arith_prim!
// prim # big -> Big
// prim # &big -> Incomplete
// &prim # big -> Big
// &prim # &big -> <prim # &big>::Output
// prim #-> big
// &prim #-> big
#[cfg(feature = "integer")]
macro_rules! arith_prim_commut {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => { $(
        arith_prim! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $T, $Incomplete;
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $Incomplete<'_> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, *self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for &$T {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $Incomplete<'_> {
                <&$Big as $Imp<$T>>::$method(rhs, *self)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, lhs);
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *lhs);
            }
        }
    )* };
}

// arith_prim!
// prim # big -> Big
// prim # &big -> FromIncomplete
// &prim # big -> Big
// &prim # &big -> FromIncomplete
// prim #-> big
// &prim #-> big
// struct FromIncomplete
// Big = FromIncomplete
// FromIncomplete -> Big
#[cfg(feature = "integer")]
macro_rules! arith_prim_noncommut {
    (
        $Big:ty;
        $func:path,
        $func_from:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $($T:ty, $Incomplete:ident, $FromIncomplete:ident;)*
    ) => { $(
        arith_prim! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $T, $Incomplete;
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$T>>::$method_from(&mut rhs, self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $FromIncomplete<'_> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$T>>::$method_from(&mut rhs, *self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for &$T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $FromIncomplete<'b> {
                <$T as $Imp<&$Big>>::$method(*self, rhs)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                $func_from(self, lhs, None);
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpFrom<$T>>::$method_from(self, *lhs);
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl Assign<$FromIncomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $FromIncomplete<'_>) {
                $func_from(self, src.lhs, Some(src.rhs));
            }
        }

        from_assign! { $FromIncomplete<'_> => $Big }
    )* };
}

// big # mul -> Big
// &big # mul -> Incomplete
// big #= mul
// struct Incomplete
// Big = Incomplete
// Incomplete -> Big
#[cfg(feature = "integer")]
macro_rules! mul_op {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $Mul:ident;
        $Incomplete:ident
    ) => {
        impl $Imp<$Mul<'_>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul<'_>) -> $Big {
                <$Big as $ImpAssign<$Mul<'_>>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Incomplete<'_> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$Mul<'_>> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Mul<'_>) {
                $func(self, rhs.lhs, rhs.rhs);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl Assign<$Incomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                <$Big as Assign<&$Big>>::assign(self, src.lhs);
                <$Big as $ImpAssign<$Mul<'_>>>::$method_assign(self, src.rhs);
            }
        }

        from_assign! { $Incomplete<'_> => $Big }
    };
}

// mul_op!
// mul # big -> Big
// mul # &big -> Incomplete
// mul #-> big
#[cfg(feature = "integer")]
macro_rules! mul_op_commut {
    (
        $Big:ty;
        $func:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $Mul:ident;
        $Incomplete:ident
    ) => {
        mul_op! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $Mul;
            $Incomplete
        }

        impl $Imp<$Big> for $Mul<'_> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$Mul<'_>>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'_> {
                <&$Big as $Imp<$Mul<'_>>>::$method(rhs, self)
            }
        }

        impl $ImpFrom<$Mul<'_>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul<'_>) {
                <$Big as $ImpAssign<$Mul<'_>>>::$method_assign(self, lhs);
            }
        }
    };
}

// mul_op!
// mul # big -> Big
// mul # &big -> FromIncomplete
// mul #-> big
// struct FromIncomplete
// Big = FromIncomplete
// FromIncomplete -> Big
#[cfg(feature = "integer")]
macro_rules! mul_op_noncommut {
    (
        $Big:ty;
        $func:path,
        $func_from:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpFrom:ident { $method_from:ident }
        $Mul:ident;
        $Incomplete:ident,
        $FromIncomplete:ident
    ) => {
        mul_op! {
            $Big;
            $func;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $Mul;
            $Incomplete
        }

        impl $Imp<$Big> for $Mul<'_> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$Mul<'_>>>::$method_from(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'_> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $ImpFrom<$Mul<'_>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul<'_>) {
                $func_from(self, lhs.lhs, lhs.rhs);
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl Assign<$FromIncomplete<'_>> for $Big {
            #[inline]
            fn assign(&mut self, src: $FromIncomplete<'_>) {
                <$Big as Assign<&$Big>>::assign(self, src.rhs);
                <$Big as $ImpFrom<$Mul<'_>>>::$method_from(self, src.lhs);
            }
        }

        from_assign! { $FromIncomplete<'_> => $Big }
    };
}

#[cfg(feature = "float")]
macro_rules! assign_round_deref {
    ($Src:ty => $Dst:ty) => {
        impl AssignRound<&$Src> for $Dst {
            type Round = <$Dst as AssignRound<$Src>>::Round;
            type Ordering = <$Dst as AssignRound<$Src>>::Ordering;
            #[inline]
            fn assign_round(&mut self, src: &$Src, round: Self::Round) -> Self::Ordering {
                <$Dst as AssignRound<$Src>>::assign_round(self, *src, round)
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! ref_math_op0_round {
    (
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete {
            $($param: $T,)*
        }

        impl AssignRound<$Incomplete> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete,
                round: $Round,
            ) -> $Ordering {
                $func(self, $(src.$param,)* round)
            }
        }
    };
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_round(&mut self, param*, Round) -> Ordering
// method_ref(&self, param*) -> Incomplete
#[cfg(feature = "float")]
macro_rules! math_op1_round {
    (
        $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Self {
            self.$method_round($($param,)* <$Round as Default>::default());
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $($param: $T),*) {
            self.$method_round($($param,)* <$Round as Default>::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            $func(self, None, $($param,)* round)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_ref(&self, param*) -> Incomplete
#[cfg(feature = "float")]
macro_rules! math_op1_no_round {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Self {
            self.$method_mut($($param),*);
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $($param: $T),*) {
            $func(self, None, $($param,)* Default::default());
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! ref_math_op1_round {
    (
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl AssignRound<$Incomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'_>,
                round: $Round,
            ) -> $Ordering {
                $func(self, Some(src.ref_self), $(src.$param,)* round)
            }
        }
    };
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_round(&mut self, &mut Self, param*, Round) -> Ordering
// method_ref(&self) -> Incomplete
#[cfg(feature = "float")]
macro_rules! math_op1_2_round {
    (
        $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $rop: Self,
            $($param: $T,)*
        ) -> (Self, Self) {
            self.$method_round(
                &mut $rop,
                $($param,)*
                <$Round as Default>::default(),
            );
            (self, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $rop: &mut Self, $($param: $T),*) {
            self.$method_round(
                $rop,
                $($param,)*
                <$Round as Default>::default(),
            );
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $rop: &mut Self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            $func(self, $rop, None, $($param,)* round)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// (Big, Big) = Incomplete
#[cfg(feature = "float")]
macro_rules! ref_math_op1_2_round {
    (
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl AssignRound<$Incomplete<'_>> for (&mut $Big, &mut $Big) {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'_>,
                round: $Round,
            ) -> $Ordering {
                $func(self.0, self.1, Some(src.ref_self), $(src.$param,)* round)
            }
        }

        impl AssignRound<$Incomplete<'_>> for ($Big, $Big) {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'_>,
                round: $Round,
            ) -> $Ordering {
                <
                    (&mut $Big, &mut $Big) as AssignRound<$Incomplete<'_>>
                >::assign_round(&mut (&mut self.0, &mut self.1), src, round)
            }
        }

        impl Assign<$Incomplete<'_>> for (&mut $Big, &mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                <Self as AssignRound<$Incomplete<'_>>>::assign_round(
                    self,
                    src,
                    <$Round as Default>::default(),
                );
            }
        }

        impl Assign<$Incomplete<'_>> for ($Big, $Big) {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                <
                    (&mut $Big, &mut $Big) as AssignRound<$Incomplete<'_>>
                >::assign_round(
                    &mut (&mut self.0, &mut self.1),
                    src,
                    <$Round as Default>::default(),
                );
            }
        }
    };
}

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_round(&mut self, &Self, param*, Round) -> Ordering
// method_ref(&mut self, &Self, param*) -> Incomplete
#[cfg(feature = "float")]
macro_rules! math_op2_round {
    (
        $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &Self, $($param: $T),*) -> Self {
            self.$method_round($op, $($param,)* <$Round as Default>::default());
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &Self, $($param: $T),*) {
            self.$method_round($op, $($param,)* <$Round as Default>::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $op: &Self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            $func(self, None, Some($op), $($param,)* round)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    };
}

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_ref(&mut self, &Self, param*) -> Incomplete
#[cfg(feature = "float")]
macro_rules! math_op2_no_round {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &Self, $($param: $T),*) -> Self {
            self.$method_mut($op, $($param),*);
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &Self, $($param: $T),*) {
            $func(self, None, Some($op), $($param,)* Default::default());
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'_> {
            $Incomplete {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    };
}

// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! ref_math_op2_round {
    (
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $op:ident $(, $param:ident: $T:ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl AssignRound<$Incomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'_>,
                round: $Round,
            ) -> $Ordering {
                $func(
                    self,
                    Some(src.ref_self),
                    Some(src.$op),
                    $(src.$param,)*
                    round,
                )
            }
        }
    };
}

// big # t -> Big
// big # &t -> Big
// &big # &t -> Incomplete
// big #= t
// big #= &t
// big #= t, Round -> Ordering
// big #= &t, Round -> Ordering
// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! arith_binary_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $T:ty;
        $Incomplete:ident
    ) => {
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut self,
                    &rhs,
                    <$Round as Default>::default(),
                );
                self
            }
        }

        impl $Imp<&$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &$T) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut self,
                    rhs,
                    <$Round as Default>::default(),
                );
                self
            }
        }

        impl<'a> $Imp<&'a $T> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $T) -> $Incomplete<'_> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    &rhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpAssign<&$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &$T) {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    rhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpAssignRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(&mut self, rhs: $T, round: $Round) -> $Ordering {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(self, &rhs, round)
            }
        }

        impl $ImpAssignRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(&mut self, rhs: &$T, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        self.as_raw(),
                        rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: &'a $T,
        }

        impl AssignRound<$Incomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Incomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// arith_binary_round!
// &big # big -> Big
// big #-> big
// &big #-> big
// big #-> big; Round -> Ordering
// &big #-> big; Round -> Ordering
#[cfg(feature = "float")]
macro_rules! arith_binary_self_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $Incomplete:ident
    ) => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $Big;
            $Incomplete
        }

        impl $Imp<$Big> for &$Big {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl $ImpFrom<$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Big) {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    self,
                    &lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFrom<&$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$Big) {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$Big> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $Big, round: $Round) -> $Ordering {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(self, &lhs, round)
            }
        }

        impl $ImpFromRound<&$Big> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: &$Big, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        lhs.as_raw(),
                        self.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// arith_binary_round!
// &big # t -> OwnedIncomplete
// struct OwnedIncomplete
// Big = OwnedIncomplete
#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_forward_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $T:ty;
        $Incomplete:ident,
        $OwnedIncomplete:ident
    ) => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T;
            $Incomplete
        }

        impl<'a> $Imp<$T> for &'a $Big {
            type Output = $OwnedIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: $T) -> $OwnedIncomplete<'a> {
                $OwnedIncomplete { lhs: self, rhs }
            }
        }

        #[derive(Debug)]
        pub struct $OwnedIncomplete<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl AssignRound<$OwnedIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $OwnedIncomplete<'_>, round: $Round) -> $Ordering {
                <$Big as AssignRound<&$OwnedIncomplete<'_>>>::assign_round(self, &src, round)
            }
        }

        impl AssignRound<&$OwnedIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: &$OwnedIncomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// arith_forward_round!
// t # big -> big
// t # &big -> OwnedIncomplete
// &t # big -> big
// &t # &big -> Incomplete
// t #-> big
// &t #-> big
// t #-> big; Round -> Ordering
// &t #-> big; Round -> Ordering
#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_commut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $T:ty;
        $Incomplete:ident,
        $OwnedIncomplete:ident
    ) => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T;
            $Incomplete, $OwnedIncomplete
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut rhs,
                    &self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $OwnedIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $OwnedIncomplete<'_> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'_> {
                <&$Big as $Imp<&$T>>::$method(rhs, self)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $T, round: $Round) -> $Ordering {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(self, &lhs, round)
            }
        }

        impl $ImpFromRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: &$T, round: $Round) -> $Ordering {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(self, lhs, round)
            }
        }
    };
}

// arith_forward_round!
// t # big -> big
// t # &big -> FromOwnedIncomplete
// &t # big -> big
// &t # &big -> FromIncomplete
// t #-> big
// &t #-> big
// t #-> big; Round -> Ordering
// &t #-> big; Round -> Ordering
// struct FromIncomplete
// Big = FromIncomplete
// struct FromOwnedIncomplete
// Big = FromOwnedIncomplete
#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_noncommut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $func_from:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $T:ty;
        $Incomplete:ident,
        $OwnedIncomplete:ident;
        $FromIncomplete:ident,
        $FromOwnedIncomplete:ident
    ) => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T;
            $Incomplete, $OwnedIncomplete
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    &mut rhs,
                    &self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $FromOwnedIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $FromOwnedIncomplete<'_> {
                $FromOwnedIncomplete { lhs: self, rhs }
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'_> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $T, round: $Round) -> $Ordering {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(self, &lhs, round)
            }
        }

        impl $ImpFromRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: &$T, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        lhs.as_raw(),
                        self.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: &'a $T,
            rhs: &'a $Big,
        }

        impl AssignRound<$FromIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $FromIncomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $FromOwnedIncomplete<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl AssignRound<$FromOwnedIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $FromOwnedIncomplete<'_>, round: $Round) -> $Ordering {
                <$Big as AssignRound<&$FromOwnedIncomplete<'_>>>::assign_round(self, &src, round)
            }
        }

        impl AssignRound<&$FromOwnedIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: &$FromOwnedIncomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// big # prim -> Big
// big # &prim -> Big
// &big # prim -> Incomplete
// &big # &prim -> Incomplete
// big #= prim
// big #= &prim
// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! arith_prim_exact_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => { $(
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl $Imp<&$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &$T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, *rhs);
                self
            }
        }

        impl<'b> $Imp<$T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: $T) -> $Incomplete<'b> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl<'b> $Imp<&$T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$T) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(
                        self.as_raw_mut(),
                        self.as_raw(),
                        rhs,
                        $raw_round(<$Round as Default>::default()),
                    );
                }
            }
        }

        impl $ImpAssign<&$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &$T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *rhs);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl AssignRound<$Incomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Incomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs,
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    )* };
}

// arith_prim_exact_round!
// big #= prim, Round -> Ordering
// big #= &prim, Round -> Ordering
#[cfg(feature = "float")]
macro_rules! arith_prim_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => { $(
        arith_prim_exact_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $T, $Incomplete;
        }

        impl $ImpAssignRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(&mut self, rhs: $T, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        self.as_raw(),
                        rhs,
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        impl $ImpAssignRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(&mut self, rhs: &$T, round: $Round) -> $Ordering {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(self, *rhs, round)
            }
        }
    )* };
}

// arith_prim_round!
// prim # big -> Big
// prim # &big -> Incomplete
// &prim # big -> Big
// &prim # &big -> Incomplete
// prim #-> big
// &prim #-> big
// prim #-> big; Round -> Ordering
// &prim #-> big; Round -> Ordering
#[cfg(feature = "float")]
macro_rules! arith_prim_commut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $($T:ty, $Incomplete:ident;)*
    ) => { $(
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T, $Incomplete;
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $Incomplete<'_> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, *self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for &$T {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(rhs, *self)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(
                    self,
                    *lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $T, round: $Round) -> $Ordering {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(self, lhs, round)
            }
        }

        impl $ImpFromRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: &$T, round: $Round) -> $Ordering {
                <$Big as $ImpFromRound<$T>>::$method_from_round(self, *lhs, round)
            }
        }
    )* };
}

// arith_prim_round!
// prim # big -> Big
// prim # &big -> FromIncomplete
// &prim # big -> Big
// &prim # &big -> FromIncomplete
// prim #-> big
// &prim #-> big
// prim #-> big; Round -> Ordering
// &prim #-> big; Round -> Ordering
// struct FromIncomplete
// Big = FromIncomplete
#[cfg(feature = "float")]
macro_rules! arith_prim_noncommut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $func_from:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $($T:ty, $Incomplete:ident, $FromIncomplete:ident;)*
    ) => { $(
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $T, $Incomplete;
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &$Big) -> $FromIncomplete<'_> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $Imp<$Big> for &$T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    &mut rhs,
                    *self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for &$T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $FromIncomplete<'b> {
                <$T as $Imp<&$Big>>::$method(*self, rhs)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFrom<&$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$T) {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    self,
                    *lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $T, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        lhs,
                        self.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        impl $ImpFromRound<&$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: &$T, round: $Round) -> $Ordering {
                <$Big as $ImpFromRound<$T>>::$method_from_round(self, *lhs, round)
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl AssignRound<$FromIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $FromIncomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        src.lhs,
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    )* };
}

// big # mul -> Big
// &big # mul -> Incomplete
// big #= mul
// big #= mul, Round -> Ordering
// struct Incomplete
// Big = Incomplete
#[cfg(feature = "float")]
macro_rules! mul_op_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $Mul:ident;
        $Incomplete:ident
    ) => {
        impl $Imp<$Mul<'_>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul<'_>) -> $Big {
                <$Big as $ImpAssignRound<$Mul<'_>>>::$method_assign_round(
                    &mut self,
                    rhs,
                    <$Round as Default>::default(),
                );
                self
            }
        }

        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Incomplete<'_> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$Mul<'_>> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Mul<'_>) {
                <$Big as $ImpAssignRound<$Mul<'_>>>::$method_assign_round(
                    self,
                    rhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpAssignRound<$Mul<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(&mut self, rhs: $Mul<'_>, round: $Round) -> $Ordering {
                let ret =
                    unsafe { $func(self.as_raw_mut(), self.as_raw(), rhs, $raw_round(round)) };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl AssignRound<$Incomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Incomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.as_raw_mut(),
                        src.lhs.as_raw(),
                        src.rhs,
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// mul_op_round!
// mul # big -> Big
// mul # &big -> Incomplete
// mul #-> big
// mul #-> big; Round -> Ordering
#[cfg(feature = "float")]
macro_rules! mul_op_commut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $Mul:ident;
        $Incomplete:ident
    ) => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $Mul;
            $Incomplete
        }

        impl $Imp<$Big> for $Mul<'_> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<$Mul<'_>>>::$method_assign_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'_> {
                <&$Big as $Imp<$Mul<'_>>>::$method(rhs, self)
            }
        }

        impl $ImpFrom<$Mul<'_>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul<'_>) {
                <$Big as $ImpAssignRound<$Mul<'_>>>::$method_assign_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$Mul<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $Mul<'_>, round: $Round) -> $Ordering {
                <$Big as $ImpAssignRound<$Mul<'_>>>::$method_assign_round(self, lhs, round)
            }
        }
    };
}

// mul_op_round!
// mul # big -> Big
// mul # &big -> FromIncomplete
// mul #-> big
// mul #-> big; Round -> Ordering
// struct FromIncomplete
// Big = FromIncomplete
#[cfg(feature = "float")]
macro_rules! mul_op_noncommut_round {
    (
        $Big:ty,
        $Round:ty =>
        $Ordering:ty;
        $func:path,
        $func_from:path,
        $raw_round:path =>
        $ord:path;
        $Imp:ident { $method:ident }
        $ImpAssign:ident { $method_assign:ident }
        $ImpAssignRound:ident { $method_assign_round:ident }
        $ImpFrom:ident { $method_from:ident }
        $ImpFromRound:ident { $method_from_round:ident }
        $Mul:ident;
        $Incomplete:ident,
        $FromIncomplete:ident
    ) => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp { $method }
            $ImpAssign { $method_assign }
            $ImpAssignRound { $method_assign_round }
            $Mul;
            $Incomplete
        }

        impl $Imp<$Big> for $Mul<'_> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$Mul<'_>>>::$method_from_round(
                    &mut rhs,
                    self,
                    <$Round as Default>::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'_> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $ImpFrom<$Mul<'_>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul<'_>) {
                <$Big as $ImpFromRound<$Mul<'_>>>::$method_from_round(
                    self,
                    lhs,
                    <$Round as Default>::default(),
                );
            }
        }

        impl $ImpFromRound<$Mul<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(&mut self, lhs: $Mul<'_>, round: $Round) -> $Ordering {
                let ret =
                    unsafe { $func_from(self.as_raw_mut(), lhs, self.as_raw(), $raw_round(round)) };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl AssignRound<$FromIncomplete<'_>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $FromIncomplete<'_>, round: $Round) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.as_raw_mut(),
                        src.lhs,
                        src.rhs.as_raw(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! static_assert {
    ($cond:expr) => {
        let _: [(); (!$cond) as usize] = [];
    };
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! static_assert_same_layout {
    ($T:ty, $U:ty) => {
        static_assert!(std::mem::size_of::<$T>() == std::mem::size_of::<$U>());
        static_assert!(std::mem::align_of::<$T>() == std::mem::align_of::<$U>());
    };
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! cast_ptr {
    ($src:expr, $T:ty) => {{
        struct Ptr<T>(*const T);
        impl<T> Ptr<T> {
            fn get(&self) -> T {
                unreachable!()
            }
        }
        let ptr = Ptr($src);
        if false {
            #[allow(unused_unsafe)]
            #[allow(clippy::transmute_ptr_to_ptr)]
            unsafe {
                let _ = std::mem::transmute::<_, $T>(ptr.get());
            }
        }
        ptr.0 as *const $T
    }};
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! cast_ptr_mut {
    ($src:expr, $T:ty) => {{
        struct Ptr<T>(*mut T);
        impl<T> Ptr<T> {
            fn get(&self) -> T {
                unreachable!()
            }
        }
        let ptr = Ptr($src);
        if false {
            #[allow(unused_unsafe)]
            #[allow(clippy::transmute_ptr_to_ptr)]
            unsafe {
                let _ = std::mem::transmute::<_, $T>(ptr.get());
            }
        }
        ptr.0 as *mut $T
    }};
}

#[cfg(any(feature = "integer", feature = "float", feature = "rand"))]
macro_rules! need_unsafe {
    () => {
        #[allow(clippy::useless_transmute)]
        {
            let _: () = std::mem::transmute(());
        }
    };
}

#[cfg(maybe_uninit)]
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! let_uninit_ptr {
    ($uninit:ident, $ptr:ident) => {
        // make this unsafe to match cfg(not(maybe_uninit))
        need_unsafe!();
        let mut $uninit = std::mem::MaybeUninit::uninit();
        let $ptr = $uninit.as_mut_ptr();
    };
    ($uninit:ident: $T:ty, $ptr:ident) => {
        // make this unsafe to match cfg(not(maybe_uninit))
        need_unsafe!();
        let mut $uninit = std::mem::MaybeUninit::<$T>::uninit();
        let $ptr = $uninit.as_mut_ptr();
    };
}

#[cfg(not(maybe_uninit))]
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! let_uninit_ptr {
    ($uninit:ident, $ptr:ident) => {
        let mut $uninit = std::mem::uninitialized();
        let $ptr = &mut $uninit as *mut _;
    };
    ($uninit:ident: $T:ty, $ptr:ident) => {
        let mut $uninit = std::mem::uninitialized::<$T>();
        let $ptr = &mut $uninit as *mut $T;
    };
}

#[cfg(maybe_uninit)]
#[cfg(feature = "rand")]
macro_rules! let_zeroed_ptr {
    ($uninit:ident, $ptr:ident) => {
        // make this unsafe to match cfg(not(maybe_uninit))
        need_unsafe!();
        let mut $uninit = std::mem::MaybeUninit::zeroed();
        let $ptr = $uninit.as_mut_ptr();
    };
    ($uninit:ident: $T:ty, $ptr:ident) => {
        // make this unsafe to match cfg(not(maybe_uninit))
        need_unsafe!();
        let mut $uninit = std::mem::MaybeUninit::<$T>::zeroed();
        let $ptr = $uninit.as_mut_ptr();
    };
}

#[cfg(not(maybe_uninit))]
#[cfg(feature = "rand")]
macro_rules! let_zeroed_ptr {
    ($uninit:ident, $ptr:ident) => {
        let mut $uninit = std::mem::zeroed();
        let $ptr = &mut $uninit as *mut _;
    };
    ($uninit:ident: $T:ty, $ptr:ident) => {
        let mut $uninit = std::mem::zeroed::<$T>();
        let $ptr = &mut $uninit as *mut $T;
    };
}

#[cfg(maybe_uninit)]
#[cfg(any(feature = "integer", feature = "float", feature = "rand"))]
macro_rules! assume_init {
    ($uninit:ident) => {
        $uninit.assume_init()
    };
}

#[cfg(not(maybe_uninit))]
#[cfg(any(feature = "integer", feature = "float", feature = "rand"))]
macro_rules! assume_init {
    ($uninit:ident) => {{
        // make this unsafe to match cfg(maybe_uninit)
        need_unsafe!();
        $uninit
    }};
}

#[cfg(gmp_limb_bits_64)]
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! small_limbs {
    () => {
        [
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
        ]
    };
    ($limb:expr) => {
        [
            $crate::misc::MaybeLimb::new($limb),
            $crate::misc::MaybeLimb::uninit(),
        ]
    };
}

#[cfg(gmp_limb_bits_32)]
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! small_limbs {
    () => {
        [
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
        ]
    };
    ($limb:expr) => {
        [
            $crate::misc::MaybeLimb::new($limb),
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
            $crate::misc::MaybeLimb::uninit(),
        ]
    };
}
