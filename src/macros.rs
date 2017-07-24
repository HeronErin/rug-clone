// Copyright © 2016–2017 University of Malta

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
macro_rules! math_op1 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> $Big {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! ref_math_op1 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! math_op1_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $rop: $Big,
            $($param: $T,)*
        ) -> ($Big, $Big) {
            self.$method_mut(&mut $rop, $($param),*);
            (self, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $rop: &mut $Big, $($param: $T),*) {
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
        ) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! ref_math_op1_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> From<$Ref<'a>> for ($Big, $Big) {
            #[inline]
            fn from(src: $Ref<'a>) -> ($Big, $Big) {
                let mut pair = <($Big, $Big) as Default>::default();
                (&mut pair.0, &mut pair.1).assign(src);
                pair
            }
        }

        impl<'a> Assign<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
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
    }
}

#[cfg(feature = "integer")]
macro_rules! math_op2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &$Big, $($param: $T),*) -> $Big {
            self.$method_mut($op, $($param),*);
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &$Big, $($param: $T),*) {
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
            $op: &'a $Big,
            $($param: $T,)*
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! ref_math_op2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $op:ident $(, $param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
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
    }
}

#[cfg(feature = "integer")]
macro_rules! math_op2_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $op: $Big,
            $($param: $T,)*
        ) -> ($Big, $Big) {
            self.$method_mut(&mut $op, $($param),*);
            (self, $op)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &mut $Big, $($param: $T),*) {
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
            $op: &'a $Big,
            $($param: $T,)*
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! ref_math_op2_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $op:ident $(, $param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> From<$Ref<'a>> for ($Big, $Big) {
            #[inline]
            fn from(src: $Ref<'a>) -> ($Big, $Big) {
                let mut pair = <($Big, $Big) as Default>::default();
                (&mut pair.0, &mut pair.1).assign(src);
                pair
            }
        }

        impl<'a> Assign<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
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
    }
}

#[cfg(feature = "integer")]
macro_rules! from_borrow {
    { $Src:ty => $Dst:ty} => {
        impl<'a> From<$Src> for $Dst {
            #[inline]
            fn from(t: $Src) -> $Dst {
                let mut ret = <$Dst>::new();
                ret.assign(t);
                ret
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_unary {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $Ref:ident
    } => {
        impl $Imp for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self) -> $Big {
                self.$method_assign();
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self) -> $Ref<'a> {
                $Ref { op: self }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            op: &'a $Big,
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, rhs: $Ref) {
                unsafe {
                    $func(self.inner_mut(), rhs.op.inner());
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_binary {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFrom:ident $method_from:ident;
        $Ref:ident
    } => {
        // x # y
        impl $Imp<$Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                self.$method(&rhs)
            }
        }

        // x # &y
        impl<'a> $Imp<&'a $Big> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'a $Big) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // &x # y
        impl<'a> $Imp<$Big> for &'a $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // x #= y
        impl $ImpAssign<$Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Big) {
                self.$method_assign(&rhs);
            }
        }

        // x #= &y
        impl<'a> $ImpAssign<&'a $Big> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
        }

        // y #from= x
        impl $ImpFrom<$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Big) {
                self.$method_from(&lhs);
            }
        }

        // y #from= &x
        impl<'a> $ImpFrom<&'a $Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }

        // &x # &y
        impl<'a> $Imp<&'a $Big> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: &'a $Big,
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Ref) {
                unsafe {
                    $func(self.inner_mut(), src.lhs.inner(), src.rhs.inner());
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_prim {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        // x # t
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // x #= t
        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), rhs.into());
                }
            }
        }

        // &x # t
        impl<'a> $Imp<$T> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Ref) {
                unsafe {
                    $func(self.inner_mut(), src.lhs.inner(), src.rhs.into());
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_prim_noncommut {
    {
        $Big:ty;
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFrom:ident $method_from:ident;
        $T:ty;
        $Ref:ident $RefFrom:ident
    } => {
        arith_prim! {
            $Big; $func; $Imp $method; $ImpAssign $method_assign; $T; $Ref
        }

        // t - y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // y -from= t
        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                unsafe {
                    $func_from(self.inner_mut(), lhs.into(), self.inner());
                }
            }
        }

        // t - &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        from_borrow! { $RefFrom<'a> => $Big }

        impl<'a> Assign<$RefFrom<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $RefFrom) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.into(),
                        src.rhs.inner()
                    );
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_prim_commut {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFrom:ident $method_from:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim! {
            $Big; $func; $Imp $method; $ImpAssign $method_assign; $T; $Ref
        }

        // t + y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        // y +from= t
        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                self.$method_assign(lhs);
            }
        }

        // t + &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                rhs.$method(self)
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! mul_op {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $Mul:ident, $rhs_method:ident;
        $Ref:ident
    } => {
        impl<'a> $Imp<$Mul<'a>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        impl<'a> $ImpAssign<$Mul<'a>> for $Big  {
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

        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone,Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        from_borrow! { $Ref<'a> => $Big }

        impl<'a> Assign<$Ref<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $Ref) {
                self.assign(src.lhs);
                self.$method_assign(src.rhs);
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! mul_op_commut {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFrom:ident $method_from:ident;
        $Mul:ident, $rhs_method:ident;
        $Ref:ident
    } => {
        mul_op! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $Mul, $rhs_method;
            $Ref
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                self.$method_assign(lhs);
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                rhs.$method(self)
            }
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! mul_op_noncommut {
    {
        $Big:ty;
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFrom:ident $method_from:ident;
        $Mul:ident, $rhs_method:ident;
        $Ref:ident $RefFrom:ident
    } => {
        mul_op! {
            $Big;
            $func;
            $Imp $method;
            $ImpAssign $method_assign;
            $Mul, $rhs_method;
            $Ref
        }

        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.lhs.inner(),
                        lhs.rhs.$rhs_method()
                    );
                }
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        from_borrow! { $RefFrom<'a> => $Big }

        impl<'a> Assign<$RefFrom<'a>> for $Big {
            #[inline]
            fn assign(&mut self, src: $RefFrom) {
                self.assign(src.rhs);
                self.$method_from(src.lhs);
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! math_op1_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> $Big {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! math_op1_no_round {
    {
        $Big:ty;
        $func:path, $raw_round:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> $Big {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! ref_math_op1_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Ref<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
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
    }
}

#[cfg(feature = "float")]
macro_rules! math_op1_2_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $($raw_round:path),* => $ord:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $rop: $Big,
            $($param: $T,)*
        ) -> ($Big, $Big) {
            self.$method_round(&mut $rop, $($param,)* Default::default());
            (self, $rop)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $rop: &mut $Big, $($param: $T),*) {
            self.$method_round($rop, $($param,)* Default::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $rop: &mut $Big,
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! ref_math_op1_2_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $($raw_round:path),* => $ord:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> Assign<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
                self.assign_round(src, Default::default());
            }
        }

        impl<'a> AssignRound<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
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
    }
}

#[cfg(feature = "float")]
macro_rules! math_op2_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $op: &$Big, $($param: $T),*) -> $Big {
            self.$method_round($op, $($param.into(),)* Default::default());
            self
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $op: &$Big, $($param: $T),*) {
            self.$method_round($op, $($param.into(),)* Default::default());
        }

        $(#[$attr_round])*
        #[inline]
        pub fn $method_round(
            &mut self,
            $op: &$Big,
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
            $op: &'a $Big,
            $($param: $T,)*
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! ref_math_op2_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $op:ident $(, $param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a $Big,
            $op: &'a $Big,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Ref<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
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
    }
}

#[cfg(feature = "float")]
macro_rules! arith_binary_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        // x # t
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // x # &t
        impl<'a> $Imp<&'a $T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: &'a $T) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // x #= t
        impl $ImpAssign<$T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $T) {
                self.$method_assign(&rhs);
            }
        }

        // x #= &t
        impl<'a> $ImpAssign<&'a $T> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: &'a $T) {
                self.$method_assign_round(rhs, Default::default());
            }
        }

        // x #= t with rounding
        impl $ImpAssignRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: $T,
                round: $Round,
            ) -> $Ordering {
                self.$method_assign_round(&rhs, round)
            }
        }

        // x #= &t with rounding
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

        // &x # &t
        impl<'a> $Imp<&'a $T> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: &'a $T,
        }

        impl<'a> AssignRound<$Ref<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Ref, round: $Round) -> $Ordering {
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
    }
}

#[cfg(feature = "float")]
macro_rules! arith_binary_self_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Ref:ident
    } => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Big;
            $Ref
        }

        // &x # y
        impl<'a> $Imp<$Big> for &'a $Big {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // y #from= x
        impl $ImpFrom<$Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Big) {
                self.$method_from(&lhs);
            }
        }

        // y #from= &x
        impl<'a> $ImpFrom<&'a $Big> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &$Big) {
                self.$method_from_round(lhs, Default::default());
            }
        }

        // y #from= x with rounding
        impl<'a> $ImpFromRound<$Big> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $Big,
                round: $Round,
            ) -> $Ordering {
                self.$method_from_round(&lhs, round)
            }
        }

        // y #from= &x with rounding
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
    }
}

#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_forward_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident
    } => {
        arith_binary_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref
        }

        // &x # t
        impl<'a> $Imp<$T> for &'a $Big {
            type Output = $RefOwn<'a>;
            #[inline]
            fn $method(self, rhs: $T) -> $RefOwn<'a> {
                $RefOwn {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone)]
        pub struct $RefOwn<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl<'a> AssignRound<$RefOwn<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $RefOwn,
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
    }
}

#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_commut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident
    } => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $RefOwn
        }

        // t + y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        // &t + y
        impl<'a> $Imp<$Big> for &'a $T {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        // t + &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $RefOwn<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefOwn<'a> {
                rhs.$method(self)
            }
        }

        // &t + &y
        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                rhs.$method(self)
            }
        }

        // y +from= t
        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                self.$method_from(&lhs);
            }
        }

        // y +from= &t
        impl<'a> $ImpFrom<&'a $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $T) {
                self.$method_from_round(lhs, Default::default());
            }
        }

        // y +from= t with rounding
        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                self.$method_from_round(&lhs, round)
            }
        }

        // y +from= &t with rounding
        impl<'a> $ImpFromRound<&'a $T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: &'a $T,
                round: $Round,
            ) -> $Ordering {
                self.$method_assign_round(lhs, round)
            }
        }
    }
}

#[cfg(all(feature = "float", any(feature = "integer", feature = "complex")))]
macro_rules! arith_noncommut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $func_from:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident $RefFrom:ident $RefFromOwn:ident
    } => {
        arith_forward_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $RefOwn
        }

        // t - y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                (&self).$method(rhs)
            }
        }

        // &t - y
        impl<'a> $Imp<$Big> for &'a $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // t - &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $RefFromOwn<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFromOwn<'a> {
                $RefFromOwn {
                    lhs: self,
                    rhs,
                }
            }
        }

        // &t - &y
        impl<'a> $Imp<&'a $Big> for &'a $T {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
            }
        }

        // y -from= t
        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                self.$method_from(&lhs);
            }
        }

        // y -from= &t
        impl<'a> $ImpFrom<&'a $T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: &'a $T) {
                self.$method_from_round(lhs, Default::default());
            }
        }

        // y -from= t with rounding
        impl $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                self.$method_from_round(&lhs, round)
            }
        }

        // y -from= &t with rounding
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


        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: &'a $T,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$RefFrom<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $RefFrom,
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

        #[derive(Clone)]
        pub struct $RefFromOwn<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$RefFromOwn<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $RefFromOwn,
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
    }
}

#[cfg(feature = "float")]
macro_rules! arith_prim_exact_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        // x # t
        impl $Imp<$T> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $T) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // x #= t
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

        // &x # t
        impl<'a> $Imp<$T> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl<'a> AssignRound<$Ref<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Ref, round: $Round) -> $Ordering {
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
    }
}

#[cfg(feature = "float")]
macro_rules! arith_prim_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_exact_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Ref
        }

        // x #= t with rounding
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
    }
}

#[cfg(feature = "float")]
macro_rules! arith_prim_commut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref
        }

        // t + y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        // t + &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                rhs.$method(self)
            }
        }

        // y +from= t
        impl $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                self.$method_assign(lhs);
            }
        }

        // y +from= t with rounding
        impl<'a> $ImpFromRound<$T> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $T,
                round: $Round,
            ) -> $Ordering {
                self.$method_assign_round(lhs, round)
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! arith_prim_noncommut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $func_from:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefFrom:ident
    } => {
        arith_prim_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref
        }

        // t - y
        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // t - &y
        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
            }
        }

        // y -from= t
        impl<'a> $ImpFrom<$T> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $T) {
                self.$method_from_round(lhs, Default::default());
            }
        }

        // y -from= t with rounding
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

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$RefFrom<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $RefFrom,
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
    }
}

#[cfg(feature = "float")]
macro_rules! mul_op_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $Mul:ident;
        $Ref:ident
    } => {
        // x # mul
        impl<'a> $Imp<$Mul<'a>> for $Big {
            type Output = $Big;
            #[inline]
            fn $method(mut self, rhs: $Mul) -> $Big {
                self.$method_assign(rhs);
                self
            }
        }

        // x #= mul
        impl<'a> $ImpAssign<$Mul<'a>> for $Big {
            #[inline]
            fn $method_assign(&mut self, rhs: $Mul) {
                self.$method_assign_round(rhs, Default::default());
            }
        }

        // x #= mul with rounding
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

        // &x # mul
        impl<'a> $Imp<$Mul<'a>> for &'a $Big {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl<'a> AssignRound<$Ref<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Ref, round: $Round) -> $Ordering {
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
    }
}

#[cfg(feature = "float")]
macro_rules! mul_op_commut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Mul:ident;
        $Ref:ident
    } => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Mul;
            $Ref
        }

        // mul + y
        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, rhs: $Big) -> $Big {
                rhs.$method(self)
            }
        }

        // mul + &y
        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                rhs.$method(self)
            }
        }

        // y +from= t
        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                self.$method_assign(lhs);
            }
        }

        // y +from= t with rounding
        impl<'a> $ImpFromRound<$Mul<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn $method_from_round(
                &mut self,
                lhs: $Mul,
                round: $Round,
            ) -> $Ordering {
                self.$method_assign_round(lhs, round)
            }
        }
    }
}

#[cfg(feature = "float")]
macro_rules! mul_op_noncommut_round {
    {
        $Big:ty, $Round:ty => $Ordering:ty;
        $func:path, $func_from:path, $raw_round:path => $ord:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Mul:ident;
        $Ref:ident $RefFrom:ident
    } => {
        mul_op_round! {
            $Big, $Round => $Ordering;
            $func, $raw_round => $ord;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $Mul;
            $Ref
        }

        // mul - y
        impl<'a> $Imp<$Big> for $Mul<'a> {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                rhs.$method_from(self);
                rhs
            }
        }

        // mul - &y
        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
            }
        }

        // y -from= mul
        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                self.$method_from_round(lhs, Default::default());
            }
        }

        // y -from= t with rounding
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

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl<'a> AssignRound<$RefFrom<'a>> for $Big {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $RefFrom,
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
    }
}

#[cfg(any(feature = "integer", feature = "float"))]
macro_rules! sum_prod {
    { $Big:ty, $zero:expr, $one:expr } => {
        impl ::std::iter::Sum for $Big {
            #[inline]
            fn sum<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = $Big>,
            {
                match iter.next() {
                    Some(first) => iter.fold(first, Add::add),
                    None => $zero,
                }
            }
        }

        impl<'a> ::std::iter::Sum<&'a $Big> for $Big {
            #[inline]
            fn sum<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = &'a $Big>,
            {
                match iter.next() {
                    Some(first) => iter.fold(first.clone(), Add::add),
                    None => $zero,
                }
            }
        }

        impl ::std::iter::Product for $Big {
            #[inline]
            fn product<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = $Big>,
            {
                match iter.next() {
                    Some(first) => iter.fold(first, Mul::mul),
                    None => $one,
                }
            }
        }

        impl<'a> ::std::iter::Product<&'a $Big> for $Big {
            #[inline]
            fn product<I>(mut iter: I) -> $Big
            where
                I: ::std::iter::Iterator<Item = &'a $Big>,
            {
                match iter.next() {
                    Some(first) => iter.fold(first.clone(), Mul::mul),
                    None => $one,
                }
            }
        }
    }
}
