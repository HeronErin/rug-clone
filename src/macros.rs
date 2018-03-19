// Copyright © 2016–2018 University of Malta

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

#[cfg(feature = "integer")]
macro_rules! assign_deref {
    ($Src: ty => $Dst: ty) => {
        impl<'a> Assign<&'a $Src> for $Dst {
            #[inline]
            fn assign(&mut self, src: &'a $Src) {
                <$Dst as Assign<$Src>>::assign(self, *src);
            }
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! from_assign {
    ($Src: ty => $Dst: ty) => {
        impl<'r> From<$Src> for $Dst {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Dst as Assign<$Src>>::assign(&mut dst, src);
                dst
            }
        }
    };

    ($Src: ty => $Dst1: ty, $Dst2: ty) => {
        impl<'r> From<$Src> for ($Dst1, $Dst2) {
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

    ($Src: ty => $Dst1: ty, $Dst2: ty, $Dst3: ty) => {
        impl<'r> From<$Src> for ($Dst1, $Dst2, $Dst3) {
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

// method(param*) -> Src
#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! math_op0 {
    (
        $(#[$attr: meta])*
        fn $method: ident($($param: ident: $T: ty),*) -> $Src: ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method($($param: $T),*) -> $Src {
            $Src {
                $($param,)*
            }
        }
    };
}

// struct Src
// Big = Src
// Src -> Big
#[cfg(feature = "integer")]
macro_rules! ref_math_op0 {
    (
        $Big: ty;
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Src: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Src {
            $($param: $T,)*
        }

        impl Assign<$Src> for $Big {
            #[inline]
            fn assign(&mut self, src: $Src) {
                unsafe {
                    $func(self.inner_mut(), $(src.$param.into()),*);
                }
            }
        }

        from_assign! { $Src => $Big }
    };
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_ref(&self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op1 {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($($param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(self.inner_mut(), self.inner(), $($param.into()),*);
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
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
        $Big: ty;
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
    };
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op1_2 {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($rop: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(
                    self.inner_mut(),
                    $rop.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(
            &self,
            $($param: $T,)*
        ) -> $Incomplete {
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
        $Big: ty;
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a, 'b, 'c> Assign<$Incomplete<'a>>
            for (&'b mut $Big, &'c mut $Big)
        {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big, $Big }
    };
}

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_ref(&mut self, &Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2 {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($op: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'a> {
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
        $Big: ty;
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $op: ident $(, $param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        src.$op.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
    };
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self, &Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2_2 {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($op: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(
                    self.inner_mut(),
                    $op.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'a> {
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
        $Big: ty;
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $op: ident $(, $param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl<'a, 'b, 'c> Assign<$Incomplete<'a>>
            for (&'b mut $Big, &'c mut $Big)
        {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.ref_self.inner(),
                        src.$op.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big, $Big }
    };
}

// method(self, Self, Self, param*) -> (Self, Self, Self)
// method_mut(&mut self, &mut Self, &mut Self, param*)
// method_mut(&mut self, &mut Self, param*) -> Incomplete
#[cfg(feature = "integer")]
macro_rules! math_op2_3 {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($op: ident, $rop: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(
                    self.inner_mut(),
                    $op.inner_mut(),
                    $rop.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'a> {
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
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $Incomplete: ident
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
                unsafe {
                    $func(self.inner_mut(), self.inner());
                }
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

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(self.inner_mut(), src.op.inner());
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
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
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpFrom: ident $method_from: ident;
        $Incomplete: ident
    ) => {
        impl $Imp<$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Big) -> $Big {
                <$Big as $ImpAssign<&$Big>>::$method_assign(&mut self, &rhs);
                self
            }
        }

        impl<'a> $Imp<&'a $Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'a $Big) -> $Big {
                <$Big as $ImpAssign<&$Big>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> $Imp<$Big> for &'a $Big {
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
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'a> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Big) {
                <$Big as $ImpAssign<&$Big>>::$method_assign(self, &rhs);
            }
        }

        impl<'a> $ImpAssign<&'a $Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
        }

        impl $ImpFrom<$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Big) {
                <$Big as $ImpFrom<&$Big>>::$method_from(self, &lhs);
            }
        }

        impl<'a> $ImpFrom<&'a $Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: &'a $Big,
        }

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(self.inner_mut(), src.lhs.inner(), src.rhs.inner());
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
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
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl<'t> $Imp<&'t $T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'t $T) -> $Big {
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

        impl<'t, 'b> $Imp<&'t $T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'t $T) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), rhs.into());
                }
            }
        }

        impl<'t> $ImpAssign<&'t $T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'t $T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *rhs);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                unsafe {
                    $func(self.inner_mut(), src.lhs.inner(), src.rhs.into());
                }
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
    };
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
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpFrom: ident $method_from: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Incomplete
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
            fn $method(self, rhs: &'b $Big) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl<'t> $Imp<$Big> for &'t $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, *self);
                rhs
            }
        }

        impl<'b, 't> $Imp<&'b $Big> for &'t $T {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> Self::Output {
                <&$Big as $Imp<$T>>::$method(rhs, *self)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, lhs);
            }
        }

        impl<'t> $ImpFrom<&'t $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'t $T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *lhs);
            }
        }
    };
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
        $Big: ty;
        $func: path, $func_from: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpFrom: ident $method_from: ident;
        $T: ty;
        $Incomplete: ident $FromIncomplete: ident
    ) => {
        arith_prim! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Incomplete
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
            fn $method(self, rhs: &'b $Big) -> $FromIncomplete<'b> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl<'t> $Imp<$Big> for &'t $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$T>>::$method_from(&mut rhs, *self);
                rhs
            }
        }

        impl<'b, 't> $Imp<&'b $Big> for &'t $T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $FromIncomplete<'b> {
                <$T as $Imp<&$Big>>::$method(*self, rhs)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                unsafe {
                    $func_from(self.inner_mut(), lhs.into(), self.inner());
                }
            }
        }

        impl<'t> $ImpFrom<&'t $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'t $T) {
                <$Big as $ImpFrom<$T>>::$method_from(self, *lhs);
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl<'a> Assign<$FromIncomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $FromIncomplete<'a>) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.into(),
                        src.rhs.inner(),
                    );
                }
            }
        }

        from_assign! { $FromIncomplete<'r> => $Big }
    };
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
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $Mul: ident, $rhs_method: ident;
        $Incomplete: ident
    ) => {
        impl<'a> $Imp<$Mul<'a>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul) -> $Big {
                <$Big as $ImpAssign<$Mul>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Incomplete<'a> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl<'a> $ImpAssign<$Mul<'a>> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Mul) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        rhs.lhs.inner(),
                        rhs.rhs.$rhs_method(),
                    );
                }
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl<'a> Assign<$Incomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'a>) {
                <$Big as Assign<&$Big>>::assign(self, src.lhs);
                <$Big as $ImpAssign<$Mul>>::$method_assign(self, src.rhs);
            }
        }

        from_assign! { $Incomplete<'r> => $Big }
    };
}

// mul_op!
// mul # big -> Big
// mul # &big -> Incomplete
// mul #-> big
#[cfg(feature = "integer")]
macro_rules! mul_op_commut {
    (
        $Big: ty;
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpFrom: ident $method_from: ident;
        $Mul: ident, $rhs_method: ident;
        $Incomplete: ident
    ) => {
        mul_op! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $Mul, $rhs_method;
            $Incomplete
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$Mul>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'a> {
                <&$Big as $Imp<$Mul>>::$method(rhs, self)
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                <$Big as $ImpAssign<$Mul>>::$method_assign(self, lhs);
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
        $Big: ty;
        $func: path, $func_from: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpFrom: ident $method_from: ident;
        $Mul: ident, $rhs_method: ident;
        $Incomplete: ident $FromIncomplete: ident
    ) => {
        mul_op! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $Mul, $rhs_method;
            $Incomplete
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$Mul>>::$method_from(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'a> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.lhs.inner(),
                        lhs.rhs.$rhs_method(),
                    );
                }
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl<'a> Assign<$FromIncomplete<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $FromIncomplete<'a>) {
                <$Big as Assign<&$Big>>::assign(self, src.rhs);
                <$Big as $ImpFrom<$Mul>>::$method_from(self, src.lhs);
            }
        }

        from_assign! { $FromIncomplete<'r> => $Big }
    };
}

#[cfg(feature = "integer")]
macro_rules! fold {
    ($Big: ty, $Imp: ident $method: ident, $ident: expr, $oper: path) => {
        impl $Imp for $Big {
            fn $method<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = $Big>,
            {
                let mut a = match iter.next() {
                    Some(first) => first,
                    None => return $ident,
                };
                let mut b = match iter.next() {
                    Some(second) => $oper(second, &a),
                    None => return a,
                };
                loop {
                    match iter.next() {
                        Some(i) => a.assign($oper(&b, &i)),
                        None => return b,
                    }
                    match iter.next() {
                        Some(i) => b.assign($oper(&a, &i)),
                        None => return a,
                    }
                }
            }
        }

        impl<'a> $Imp<&'a $Big> for $Big {
            fn $method<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = &'a $Big>,
            {
                let mut a = match iter.next() {
                    Some(first) => first.clone(),
                    None => return $ident,
                };
                let mut b = match iter.next() {
                    Some(second) => From::from($oper(second, &a)),
                    None => return a,
                };
                loop {
                    match iter.next() {
                        Some(i) => a.assign($oper(&b, i)),
                        None => return b,
                    }
                    match iter.next() {
                        Some(i) => b.assign($oper(&a, i)),
                        None => return a,
                    }
                }
            }
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! fold_in_place {
    ($Big: ty, $Imp: ident $method: ident, $ident: expr, $op_assign: path) => {
        impl $Imp for $Big {
            fn $method<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = $Big>,
            {
                let mut acc = match iter.next() {
                    Some(first) => first,
                    None => return $ident,
                };
                for i in iter {
                    $op_assign(&mut acc, i);
                }
                acc
            }
        }

        impl<'a> $Imp<&'a $Big> for $Big {
            fn $method<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = &'a $Big>,
            {
                let mut acc = match iter.next() {
                    Some(first) => first.clone(),
                    None => return $ident,
                };
                for i in iter {
                    $op_assign(&mut acc, i);
                }
                acc
            }
        }
    };
}

#[cfg(feature = "float")]
macro_rules! assign_round_deref {
    ($Src: ty => $Dst: ty) => {
        impl<'a> AssignRound<&'a $Src> for $Dst {
            type Round = <$Dst as AssignRound<$Src>>::Round;
            type Ordering = <$Dst as AssignRound<$Src>>::Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: &'a $Src,
                round: Self::Round,
            ) -> Self::Ordering {
                <$Dst as AssignRound<$Src>>::assign_round(self, *src, round)
            }
        }
    };
}

// struct Src
// Big = Src
#[cfg(feature = "float")]
macro_rules! ref_math_op0_round {
    (
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $(#[$attr_ref: meta])*
        struct $Src: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Src {
            $($param: $T,)*
        }

        impl AssignRound<$Src> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Src, round: $Round,) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        $(src.$param.into(),)*
                        $raw_round(round),
                    )
                };
                $ord(ret)
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
        $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $(#[$attr: meta])*
        fn $method: ident($($param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Self {
            self.$method_round($($param,)* Default::default());
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $($param: $T),*) {
            self.$method_round($($param,)* Default::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            let ret = unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    $raw_round(round),
                )
            };
            $ord(ret)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
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
        $func: path, $raw_round: path;
        $(#[$attr: meta])*
        fn $method: ident($($param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
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
            unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    $raw_round(Default::default()),
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Incomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                        $raw_round(round),
                    )
                };
                $ord(ret)
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
        $Round: ty => $Ordering: ty;
        $func: path, $($raw_round: path),* => $ord: path;
        $(#[$attr: meta])*
        fn $method: ident($rop: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $rop: Self,
            $($param: $T,)*
        ) -> (Self, Self) {
            self.$method_round(&mut $rop, $($param,)* Default::default());
            (self, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $rop: &mut Self, $($param: $T),*) {
            self.$method_round($rop, $($param,)* Default::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $rop: &mut Self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            let ret = unsafe {
                $func(
                    self.inner_mut(),
                    $rop.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    $($raw_round(round),)*
                )
            };
            $ord(ret)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $($raw_round: path),* => $ord: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a, 'b, 'c> AssignRound<$Incomplete<'a>>
            for (&'b mut $Big, &'c mut $Big)
        {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                        $($raw_round(round),)*
                    )
                };
                $ord(ret)
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
        $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $(#[$attr: meta])*
        fn $method: ident($op: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &Self, $($param: $T),*) -> Self {
            self.$method_round($op, $($param.into(),)* Default::default());
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &Self, $($param: $T),*) {
            self.$method_round($op, $($param.into(),)* Default::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $op: &Self,
            $($param: $T,)*
            round: $Round,
        ) -> $Ordering {
            let ret = unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                    $raw_round(round),
                )
            };
            $ord(ret)
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a Self,
            $($param: $T,)*
        ) -> $Incomplete<'a> {
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $op: ident $(, $param: ident: $T: ty),* }
    ) => {
        $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Incomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        src.$op.inner(),
                        $(src.$param.into(),)*
                        $raw_round(round),
                    )
                };
                $ord(ret)
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut self,
                    &rhs,
                    Default::default(),
                );
                self
            }
        }

        impl<'a> $Imp<&'a $T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'a $T) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut self,
                    rhs,
                    Default::default(),
                );
                self
            }
        }

        impl<'a> $Imp<&'a $T> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $T) -> $Incomplete<'a> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    &rhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpAssign<&'a $T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'a $T) {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    rhs,
                    Default::default(),
                );
            }
        }

        impl $ImpAssignRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    &rhs,
                    round,
                )
            }
        }

        impl<'a> $ImpAssignRound<&'a $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: &'a $T,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.inner(),
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

        impl<'a> AssignRound<$Incomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $Incomplete: ident
    ) => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Big;
            $Incomplete
        }

        impl<'a> $Imp<$Big> for &'a $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    &mut rhs,
                    self,
                    Default::default(),
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
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFrom<&'a $Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$Big) {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    self,
                    lhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFromRound<$Big> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $Big,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpFromRound<&$Big>>::$method_from_round(
                    self,
                    &lhs,
                    round,
                )
            }
        }

        impl<'a> $ImpFromRound<&'a $Big> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'a $Big,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident
    ) => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
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

        impl<'a> AssignRound<$OwnedIncomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $OwnedIncomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                <$Big as AssignRound<&$OwnedIncomplete>>::assign_round(
                    self,
                    &src,
                    round,
                )
            }
        }

        impl<'a, 'b> AssignRound<&'a $OwnedIncomplete<'b>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: &'a $OwnedIncomplete<'b>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident
    ) => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete $OwnedIncomplete
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut rhs,
                    &self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $OwnedIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $OwnedIncomplete<'a> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl<'a> $Imp<$Big> for &'a $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    &mut rhs,
                    self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'a> {
                <&$Big as $Imp<&$T>>::$method(rhs, self)
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFrom<&'a $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    lhs,
                    Default::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    round,
                )
            }
        }

        impl<'a> $ImpFromRound<&'a $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'a $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpAssignRound<&$T>>::$method_assign_round(
                    self,
                    lhs,
                    round,
                )
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $func_from: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident;
        $FromIncomplete: ident $FromOwnedIncomplete: ident
    ) => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete $OwnedIncomplete
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    &mut rhs,
                    &self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $FromOwnedIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromOwnedIncomplete<'a> {
                $FromOwnedIncomplete { lhs: self, rhs }
            }
        }

        impl<'a> $Imp<$Big> for &'a $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    &mut rhs,
                    self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'a> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFrom<&'a $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $T) {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    lhs,
                    Default::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpFromRound<&$T>>::$method_from_round(
                    self,
                    &lhs,
                    round,
                )
            }
        }

        impl<'a> $ImpFromRound<&'a $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'a $T,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
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

        impl<'a> AssignRound<$FromIncomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $FromIncomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
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

        impl<'a> AssignRound<$FromOwnedIncomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $FromOwnedIncomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                <$Big as AssignRound<&$FromOwnedIncomplete>>::assign_round(
                    self,
                    &src,
                    round,
                )
            }
        }

        impl<'a, 'b> AssignRound<&'a $FromOwnedIncomplete<'b>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: &'a $FromOwnedIncomplete<'b>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut self, rhs);
                self
            }
        }

        impl<'t> $Imp<&'t $T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'t $T) -> $Big {
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

        impl<'t, 'b> $Imp<&'t $T> for &'b $Big {
            type Output = $Incomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'t $T) -> $Incomplete<'b> {
                <&$Big as $Imp<$T>>::$method(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        $raw_round(Default::default()),
                    );
                }
            }
        }

        impl<'t> $ImpAssign<&'t $T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'t $T) {
                <$Big as $ImpAssign<$T>>::$method_assign(self, *rhs);
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl<'a> AssignRound<$Incomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.into(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
}

// arith_prim_exact_round!
// big #= prim, Round -> Ordering
// big #= &prim, Round -> Ordering
#[cfg(feature = "float")]
macro_rules! arith_prim_round {
    (
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_exact_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Incomplete
        }

        impl $ImpAssignRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: $T,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        impl<'t> $ImpAssignRound<&'t $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: &'t $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(
                    self,
                    *rhs,
                    round,
                )
            }
        }
    };
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete
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
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'a> {
                <&$Big as $Imp<$T>>::$method(rhs, self)
            }
        }

        impl<'t> $Imp<$Big> for &'t $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, *self);
                rhs
            }
        }

        impl<'b, 't> $Imp<&'b $Big> for &'t $T {
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
                    Default::default(),
                );
            }
        }

        impl<'t> $ImpFrom<&'t $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'t $T) {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(
                    self,
                    *lhs,
                    Default::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpAssignRound<$T>>::$method_assign_round(
                    self,
                    lhs,
                    round,
                )
            }
        }

        impl<'t> $ImpFromRound<&'t $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'t $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    self,
                    *lhs,
                    round,
                )
            }
        }
    };
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $func_from: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $FromIncomplete: ident
    ) => {
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    &mut rhs,
                    self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $FromIncomplete<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $FromIncomplete<'b> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl<'t> $Imp<$Big> for &'t $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    &mut rhs,
                    *self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'b, 't> $Imp<&'b $Big> for &'t $T {
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
                    Default::default(),
                );
            }
        }

        impl<'t> $ImpFrom<&'t $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'t $T) {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    self,
                    *lhs,
                    Default::default(),
                );
            }
        }

        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.into(),
                        self.inner(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        impl<'t> $ImpFromRound<&'t $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'t $T,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpFromRound<$T>>::$method_from_round(
                    self,
                    *lhs,
                    round,
                )
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$FromIncomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $FromIncomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.into(),
                        src.rhs.inner(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }
    };
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $Mul: ident;
        $Incomplete: ident
    ) => {
        impl<'a> $Imp<$Mul<'a>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul) -> $Big {
                <$Big as $ImpAssignRound<$Mul>>::$method_assign_round(
                    &mut self,
                    rhs,
                    Default::default(),
                );
                self
            }
        }

        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Incomplete<'a> {
                $Incomplete { lhs: self, rhs }
            }
        }

        impl<'a> $ImpAssign<$Mul<'a>> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Mul) {
                <$Big as $ImpAssignRound<$Mul>>::$method_assign_round(
                    self,
                    rhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpAssignRound<$Mul<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: $Mul,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs,
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl<'a> AssignRound<$Incomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Incomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $Mul: ident;
        $Incomplete: ident
    ) => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Mul;
            $Incomplete
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssignRound<$Mul>>::$method_assign_round(
                    &mut rhs,
                    self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Incomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Incomplete<'a> {
                <&$Big as $Imp<$Mul>>::$method(rhs, self)
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                <$Big as $ImpAssignRound<$Mul>>::$method_assign_round(
                    self,
                    lhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFromRound<$Mul<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $Mul,
                round: $Round,
            ) -> $Ordering {
                <$Big as $ImpAssignRound<$Mul>>::$method_assign_round(
                    self,
                    lhs,
                    round,
                )
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
        $Big: ty, $Round: ty => $Ordering: ty;
        $func: path, $func_from: path, $raw_round: path => $ord: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $Mul: ident;
        $Incomplete: ident $FromIncomplete: ident
    ) => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Mul;
            $Incomplete
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFromRound<$Mul>>::$method_from_round(
                    &mut rhs,
                    self,
                    Default::default(),
                );
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $FromIncomplete<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $FromIncomplete<'a> {
                $FromIncomplete { lhs: self, rhs }
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                <$Big as $ImpFromRound<$Mul>>::$method_from_round(
                    self,
                    lhs,
                    Default::default(),
                );
            }
        }

        impl<'a> $ImpFromRound<$Mul<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $Mul,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs,
                        self.inner(),
                        $raw_round(round),
                    )
                };
                $ord(ret)
            }
        }

        #[derive(Debug)]
        pub struct $FromIncomplete<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$FromIncomplete<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $FromIncomplete<'a>,
                round: $Round,
            ) -> $Ordering {
                let ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs,
                        src.rhs.inner(),
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
    ($cond: expr) => {
        let _: [(); (!$cond) as usize] = [];
    };
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! static_assert_size {
    ($T: ty, $U: ty) => {
        let _ = |t: $T| unsafe { ::std::mem::transmute::<_, $U>(t) };
    };
    ($T: ty: $size: expr) => {
        static_assert_size!($T, [u8; $size as usize]);
    };
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! cast_ptr {
    ($src: expr, $T: ty) => {{
        struct Ptr<T>(*const T);
        impl<T> Ptr<T> {
            fn get(&self) -> T {
                unreachable!()
            }
        }
        let ptr = Ptr($src);
        if false {
            #[allow(unused_unsafe)]
            unsafe {
                #[allow(unknown_lints, useless_transmute)]
                let _ = ::std::mem::transmute::<_, $T>(ptr.get());
            }
        }
        ptr.0 as *const $T
    }};
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! cast_ptr_mut {
    ($src: expr, $T: ty) => {{
        struct Ptr<T>(*mut T);
        impl<T> Ptr<T> {
            fn get(&self) -> T {
                unreachable!()
            }
        }
        let ptr = Ptr($src);
        if false {
            #[allow(unused_unsafe)]
            unsafe {
                #[allow(unknown_lints, useless_transmute)]
                let _ = ::std::mem::transmute::<_, $T>(ptr.get());
            }
        }
        ptr.0 as *mut $T
    }};
}
