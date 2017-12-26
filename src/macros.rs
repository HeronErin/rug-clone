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
macro_rules! from_assign_to {
    { $Src:ty => $Dst:ty} => {
        impl<'r> From<$Src> for $Dst {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<$Dst>::assign_to(src, &mut dst);
                dst
            }
        }
    };

    { ref $Src:ty => $Dst:ty} => {
        impl<'a, 'r> From<&'a $Src> for $Dst {
            #[inline]
            fn from(src: &'a $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<$Dst>::assign_to(*src, &mut dst);
                dst
            }
        }
    };

    { $Src:ty => $Dst1:ty, $Dst2:ty} => {
        impl<'r> From<$Src> for ($Dst1, $Dst2) {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<(&mut $Dst1, &mut $Dst2)>>::assign_to(
                    src,
                    &mut (&mut dst.0, &mut dst.1),
                );
                dst
            }
        }
    };

    { ref $Src:ty => $Dst1:ty, $Dst2:ty} => {
        impl<'a, 'r> From<&'a $Src> for ($Dst1, $Dst2) {
            #[inline]
            fn from(src: &'a $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<(&mut $Dst1, &mut $Dst2)>>::assign_to(
                    *src,
                    &mut (&mut dst.0, &mut dst.1),
                );
                dst
            }
        }
    };

    { $Src:ty => $Dst1:ty, $Dst2:ty, $Dst3: ty} => {
        impl<'r> From<$Src> for ($Dst1, $Dst2, $Dst3) {
            #[inline]
            fn from(src: $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<
                    (&mut $Dst1, &mut $Dst2, &mut $Dst3),
                >>::assign_to(
                    src,
                    &mut (&mut dst.0, &mut dst.1, &mut dst.2),
                );
                dst
            }
        }
    };

    { ref $Src:ty => $Dst1:ty, $Dst2:ty, $Dst3: ty} => {
        impl<'a, 'r> From<&'a $Src> for ($Dst1, $Dst2, $Dst3) {
            #[inline]
            fn from(src: &'a $Src) -> Self {
                let mut dst = <Self as Default>::default();
                <$Src as AssignTo<
                    (&mut $Dst1, &mut $Dst2, &mut $Dst3),
                >>::assign_to(
                    *src,
                    &mut (&mut dst.0, &mut dst.1, &mut dst.2),
                );
                dst
            }
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! assign_to {
    { $Src:ty => $Dst:ty } => {
        impl<'a> AssignTo<$Dst> for &'a $Src {
            #[inline]
            fn assign_to(self, dst: &mut $Dst) {
                <$Src as AssignTo<$Dst>>::assign_to(*self, dst);
            }

            #[inline]
            fn to_new(self) -> $Dst {
                <$Src as AssignTo<$Dst>>::to_new(*self)
            }
        }
    };

    { ref $Ref:ty => $Dst:ty } => {
        impl<'a, 'r: 'a> AssignTo<$Dst> for &'a $Ref {
            #[inline]
            fn assign_to(self, dst: &mut $Dst) {
                <$Ref as AssignTo<$Dst>>::assign_to(*self, dst);
            }

            #[inline]
            fn to_new(self) -> $Dst {
                <$Ref as AssignTo<$Dst>>::to_new(*self)
            }
        }
    };

    { $Src:ty => $Dst1:ty, $Dst2:ty } => {
        impl<'a, 'b, 'c> AssignTo<(&'a mut $Dst1, &'b mut $Dst2)> for &'c $Src {
            #[inline]
            fn assign_to(self, dst: &mut (&'a mut $Dst1, &'b mut $Dst2)) {
                <$Src as AssignTo<
                    (&mut $Dst1, &mut $Dst2),
                >>::assign_to(*self, dst);
            }
        }
    };

    { ref $Ref:ty => $Dst1:ty, $Dst2:ty } => {
        impl<'a, 'b, 'c, 'r: 'c>
            AssignTo<(&'a mut $Dst1, &'b mut $Dst2)> for &'c $Ref
        {
            #[inline]
            fn assign_to(self, dst: &mut (&'a mut $Dst1, &'b mut $Dst2)) {
                <$Ref as AssignTo<
                    (&'a mut $Dst1, &'b mut $Dst2),
                >>::assign_to(*self, dst);
            }
        }
    };

    { ref $Ref:ty => $Dst1:ty, $Dst2:ty, $Dst3:ty } => {
        impl<'a, 'b, 'c, 'd, 'r: 'd>
            AssignTo<(&'a mut $Dst1, &'b mut $Dst2, &'c mut $Dst3)> for &'d $Ref
        {
            #[inline]
            fn assign_to(
                self,
                dst: &mut (&'a mut $Dst1, &'b mut $Dst2, &'c mut $Dst3),
            ) {
                <$Ref as AssignTo<
                    (&'a mut $Dst1, &'b mut $Dst2, &'c mut $Dst3),
                >>::assign_to(*self, dst);
            }
        }
    }
}

// method(param*) -> Src
#[cfg(feature = "integer")]
macro_rules! math_op0 {
    {
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*) -> $Src:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method($($param: $T),*) -> $Src {
            $Src {
                $($param,)*
            }
        }
    }
}

// struct Src
// AssignTo<Big> for Src
// AssignTo<Big> for &Src
#[cfg(feature = "integer")]
macro_rules! ref_math_op0 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Src:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Src {
            $($param: $T,)*
        }

        impl AssignTo<$Big> for $Src {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(dst.inner_mut(), $(self.$param.into()),*);
                }
            }
        }

        assign_to!{ $Src => $Big }
    }
}

// struct Src
// AssignTo<(Big, Big)> for Src
// Src -> (Big, Big)
// AssignTo<(Big, Big)> for &Src
// &Src -> (Big, Big)
#[cfg(feature = "integer")]
macro_rules! ref_math_op0_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Src:ident { $($param:ident: $T:ty),* }
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Src {
            $($param: $T,)*
        }

        impl<'a, 'b> AssignTo<(&'a mut $Big, &'b mut $Big)> for $Src {
            #[inline]
            fn assign_to(self, dst: &mut (&'a mut $Big, &'b mut $Big)) {
                unsafe {
                    $func(
                        dst.0.inner_mut(),
                        dst.1.inner_mut(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        from_assign_to!{ $Src => $Big, $Big }
        assign_to!{ $Src => $Big,  $Big }
        from_assign_to!{ ref $Src => $Big, $Big }
    }
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_ref(&self, param*) -> Ref
#[cfg(feature = "integer")]
macro_rules! math_op1 {
    {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

// struct Ref
// AssignTo<Big> for Ref
// AssignTo<Big> for &Ref
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

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(
                        dst.inner_mut(),
                        self.ref_self.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self) -> Ref
#[cfg(feature = "integer")]
macro_rules! math_op1_2 {
    {
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
        ) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

// struct Ref
// AssignTo<(Big, Big)> for Ref
// Ref -> (Big, Big)
// AssignTo<(Big, Big)> for &Ref
// &Ref -> (Big, Big)
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

        impl<'a, 'b, 'c> AssignTo<(&'a mut $Big, &'b mut $Big)> for $Ref<'c> {
            #[inline]
            fn assign_to(self, dst: &mut (&'a mut $Big, &'b mut $Big)) {
                unsafe {
                    $func(
                        dst.0.inner_mut(),
                        dst.1.inner_mut(),
                        self.ref_self.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        from_assign_to!{ $Ref<'r> => $Big, $Big }
        assign_to!{ ref $Ref<'r> => $Big, $Big }
        from_assign_to!{ ref $Ref<'r> => $Big, $Big }
    }
}

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_ref(&mut self, &Self, param*) -> Ref
#[cfg(feature = "integer")]
macro_rules! math_op2 {
    {
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
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

// struct Ref
// AssignTo<Big> for Ref
// AssignTo<Big> for &Ref
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

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(
                        dst.inner_mut(),
                        self.ref_self.inner(),
                        self.$op.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_ref(&self, &Self, param*) -> Ref
#[cfg(feature = "integer")]
macro_rules! math_op2_2 {
    {
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
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

// struct Ref
// AssignTo<(Big, Big)> for Ref
// Ref -> (Big, Big)
// AssignTo<(Big, Big)> for &Ref
// &Ref -> (Big, Big)
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

        impl<'a, 'b, 'c> AssignTo<(&'a mut $Big, &'b mut $Big)> for $Ref<'c> {
            #[inline]
            fn assign_to(self, dst: &mut (&'a mut $Big, &'b mut $Big)) {
                unsafe {
                    $func(
                        dst.0.inner_mut(),
                        dst.1.inner_mut(),
                        self.ref_self.inner(),
                        self.$op.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        from_assign_to!{ $Ref<'r> => $Big, $Big }
        assign_to!{ ref $Ref<'r> => $Big, $Big }
        from_assign_to!{ ref $Ref<'r> => $Big, $Big }
    }
}

// method(self, Self, Self, param*) -> (Self, Self, Self)
// method_mut(&mut self, &mut Self, &mut Self, param*)
// method_mut(&mut self, &mut Self, param*) -> Ref
#[cfg(feature = "integer")]
macro_rules! math_op2_3 {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident, $rop: ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
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
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

// struct Ref
// AssignTo<(Big, Big, Big)> for Ref
// Ref -> (Big, Big, Big)
// AssignTo<(Big, Big, Big)> for &Ref
// &Ref -> (Big, Big, Big)
#[cfg(feature = "integer")]
macro_rules! ref_math_op2_3 {
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

        impl<'a, 'b, 'c, 'd>
            AssignTo<(&'a mut $Big, &'b mut $Big, &'c mut $Big)> for $Ref<'d>
        {
            #[inline]
            fn assign_to(
                self,
                dst: &mut (&'a mut $Big, &'b mut $Big, &'c mut $Big),
            ) {
                unsafe {
                    $func(
                        dst.0.inner_mut(),
                        dst.1.inner_mut(),
                        dst.2.inner_mut(),
                        self.ref_self.inner(),
                        self.$op.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        from_assign_to!{ $Ref<'r> => $Big, $Big, $Big }
        assign_to!{ ref $Ref<'r> => $Big, $Big, $Big }
        from_assign_to!{ ref $Ref<'r> => $Big, $Big, $Big }
    }
}

// #big -> Big
// big #=
// #&big -> Ref
// struct Ref
// Ref -> Big
// big = Ref
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

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(dst.inner_mut(), self.op.inner());
                }
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// big # big -> Big
// big # &big -> Big
// &big # big -> Big
// &big # &big -> Ref
// big #= big
// big #= &big
// big #-> big
// &big #-> big
// struct Ref
// Ref -> Big
// big = Ref
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
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

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: &'a $Big,
        }

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(dst.inner_mut(), self.lhs.inner(), self.rhs.inner());
                }
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// big # prim -> Big
// big # &prim -> Big
// &big # prim -> Ref
// &big # &prim -> Ref
// big #= prim
// big #= &prim
// struct Ref
// Ref -> Big
// big = Ref
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
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: $T) -> $Ref<'b> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        impl<'t, 'b> $Imp<&'t $T> for &'b $Big {
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: &'t $T) -> $Ref<'b> {
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

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $T,
        }

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func(dst.inner_mut(), self.lhs.inner(), self.rhs.into());
                }
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// arith_prim!
// prim # big -> Big
// prim # &big -> Ref
// &prim # big -> Big
// &prim # &big -> <prim # &big>::Output
// prim #-> big
// &prim #-> big
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

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $Ref<'b> {
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
            type Output = $Ref<'b>;
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
    }
}

// arith_prim!
// prim # big -> Big
// prim # &big -> RefFrom
// &prim # big -> Big
// &prim # &big -> RefFrom
// prim #-> big
// &prim #-> big
// struct RefFrom
// RefFrom -> Big
// big = RefFrom
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

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpFrom<$T>>::$method_from(&mut rhs, self);
                rhs
            }
        }

        impl<'b> $Imp<&'b $Big> for $T {
            type Output = $RefFrom<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $RefFrom<'b> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
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
            type Output = $RefFrom<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $RefFrom<'b> {
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

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $T,
            rhs: &'a $Big,
        }

        impl<'a> AssignTo<$Big> for $RefFrom<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                unsafe {
                    $func_from(
                        dst.inner_mut(),
                        self.lhs.into(),
                        self.rhs.inner()
                    );
                }
            }
        }

        assign_to!{ ref $RefFrom<'r> => $Big }
    }
}

// big # mul -> Big
// &big # mul -> Ref
// big #= mul
// struct Ref
// Ref -> Big
// big = Ref
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
                <$Big as $ImpAssign<$Mul>>::$method_assign(&mut self, rhs);
                self
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

        #[derive(Clone,Copy)]
        pub struct $Ref<'a> {
            lhs: &'a $Big,
            rhs: $Mul<'a>,
        }

        impl<'a> AssignTo<$Big> for $Ref<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                <$Big as Assign<&$Big>>::assign(dst, self.lhs);
                <$Big as $ImpAssign<$Mul>>::$method_assign(dst, self.rhs);
            }
        }

        assign_to!{ ref $Ref<'r> => $Big }
    }
}

// mul_op!
// mul # big -> Big
// mul # &big -> Ref
// mul #-> big
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
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$Mul>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $Mul<'a> {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                <&$Big as $Imp<$Mul>>::$method(rhs, self)
            }
        }

        impl<'a> $ImpFrom<$Mul<'a>> for $Big {
            #[inline]
            fn $method_from(&mut self, lhs: $Mul) {
                <$Big as $ImpAssign<$Mul>>::$method_assign(self, lhs);
            }
        }
    }
}

// mul_op!
// mul # big -> Big
// mul # &big -> RefFrom
// mul #-> big
// struct RefFrom
// RefFrom -> Big
// big = RefFrom
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
                <$Big as $ImpFrom<$Mul>>::$method_from(&mut rhs, self);
                rhs
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

        #[derive(Clone, Copy)]
        pub struct $RefFrom<'a> {
            lhs: $Mul<'a>,
            rhs: &'a $Big,
        }

        impl<'a> AssignTo<$Big> for $RefFrom<'a> {
            #[inline]
            fn assign_to(self, dst: &mut $Big) {
                <$Big as Assign<&$Big>>::assign(dst, self.rhs);
                <$Big as $ImpFrom<$Mul>>::$method_from(dst, self.lhs);
            }
        }

        assign_to!{ ref $RefFrom<'r> => $Big }
    }
}

// lhs = &rhs
#[cfg(feature = "float")]
macro_rules! assign_round_ref {
    { $Lhs:ty: $Rhs:ty } => {
        impl<'a> AssignRound<&'a $Rhs> for $Lhs {
            type Round = <$Lhs as AssignRound<$Rhs>>::Round;
            type Ordering = <$Lhs as AssignRound<$Rhs>>::Ordering;
            #[inline]
            fn assign_round(&mut self, r: &'a $Rhs, round: Round) -> Ordering {
                <$Lhs as AssignRound<$Rhs>>::assign_round(self, *r, round)
            }
        }
    }
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_round(&mut self, param*, Round) -> Ordering
// method_ref(&self, param*) -> Ref
#[cfg(feature = "float")]
macro_rules! math_op1_round {
    {
        $Round:ty => $Ordering:ty;
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

// method(self, param*) -> Self
// method_mut(&mut self, param*)
// method_ref(&self, param*) -> Ref
#[cfg(feature = "float")]
macro_rules! math_op1_no_round {
    {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

// struct Ref
// big = Ref, Round -> Ordering
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

// method(self, Self, param*) -> (Self, Self)
// method_mut(&mut self, &mut Self, param*)
// method_round(&mut self, &mut Self, param*, Round) -> Ordering
// method_ref(&self) -> Ref
#[cfg(feature = "float")]
macro_rules! math_op1_2_round {
    {
        $Round:ty => $Ordering:ty;
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

// struct Ref
// (&mut Big, &mut Big) = Ref
// (&mut Big, &mut Big) = Ref, Round -> Ordering
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

        impl<'a> Assign<$Ref<'a>> for ($Big, $Big) {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
                <(&mut $Big, &mut $Big) as AssignRound<$Ref>>::assign_round(
                    &mut (&mut self.0, &mut self.1),
                    src,
                    Default::default(),
                );
            }
        }

        impl<'a, 'b, 'c> Assign<$Ref<'a>> for (&'b mut $Big, &'c mut $Big) {
            #[inline]
            fn assign(&mut self, src: $Ref<'a>) {
                <(&mut $Big, &mut $Big) as AssignRound<$Ref>>::assign_round(
                    &mut (self.0, self.1),
                    src,
                    Default::default(),
                );
            }
        }

        impl<'a> AssignRound<$Ref<'a>> for ($Big, $Big) {
            type Round = $Round;
            type Ordering = $Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
                round: $Round,
            ) -> $Ordering {
                <(&mut $Big, &mut $Big) as AssignRound<$Ref>>::assign_round(
                    &mut (&mut self.0, &mut self.1),
                    src,
                    round,
                )
            }
        }

        impl<'a, 'b, 'c> AssignRound<$Ref<'a>>
            for (&'b mut $Big, &'c mut $Big)
        {
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

// method(self, &Self, param*) -> Self
// method_mut(&mut self, &Self, param*)
// method_round(&mut self, &Self, param*, Round) -> Ordering
// method_ref(&mut self, &Self, param*) -> Ref
#[cfg(feature = "float")]
macro_rules! math_op2_round {
    {
        $Round:ty => $Ordering:ty;
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
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op,
                $($param,)*
            }
        }
    }
}

// struct Ref
// big = Ref, Round -> Ordering
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

// big # t -> Big
// big # &t -> Big
// &big # &t -> Ref
// big #= t
// big #= &t
// big #= t, Round -> Ordering
// big #= &t, Round -> Ordering
// struct Ref
// big = Ref, Round -> Ordering
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
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

// arith_binary_round!
// &big # big -> Big
// big #-> big
// &big #-> big
// big #-> big; Round -> Ordering
// &big #-> big; Round -> Ordering
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
    }
}

// arith_binary_round!
// &big # t -> RefOwn
// struct RefOwn
// Big = RefOwn, Round -> Ordering
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

// arith_forward_round!
// t # big -> big
// t # &big -> RefOwn
// &t # big -> big
// &t # &big -> Ref
// t #-> big
// &t #-> big
// t #-> big; Round -> Ordering
// &t #-> big; Round -> Ordering
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
            type Output = $RefOwn<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefOwn<'a> {
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
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
                    round
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
    }
}

// arith_forward_round!
// t # big -> big
// t # &big -> RefFromOwn
// &t # big -> big
// &t # &big -> RefFrom
// t #-> big
// &t #-> big
// t #-> big; Round -> Ordering
// &t #-> big; Round -> Ordering
// struct RefFrom
// big = RefFrom, Round -> Ordering
// struct RefFromOwn
// big = RefFromOwn, Round -> Ordering
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
            type Output = $RefFromOwn<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFromOwn<'a> {
                $RefFromOwn {
                    lhs: self,
                    rhs,
                }
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
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
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

// big # prim -> Big
// big # &prim -> Big
// &big # prim -> Ref
// &big # &prim -> Ref
// big #= prim
// big #= &prim
// struct Ref
// big = Ref, Round -> Ordering
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
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: $T) -> $Ref<'b> {
                $Ref {
                    lhs: self,
                    rhs,
                }
            }
        }

        impl<'t, 'b> $Imp<&'t $T> for &'b $Big {
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: &'t $T) -> $Ref<'b> {
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

// arith_prim_exact_round!
// big #= prim, Round -> Ordering
// big #= &prim, Round -> Ordering
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
    }
}

// arith_prim_round!
// prim # big -> Big
// prim # &big -> Ref
// &prim # big -> Big
// &prim # &big -> Ref
// prim #-> big
// &prim #-> big
// prim #-> big; Round -> Ordering
// &prim #-> big; Round -> Ordering
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

        impl $Imp<$Big> for $T {
            type Output = $Big;
            #[inline]
            fn $method(self, mut rhs: $Big) -> $Big {
                <$Big as $ImpAssign<$T>>::$method_assign(&mut rhs, self);
                rhs
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
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
            type Output = $Ref<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $Ref<'b> {
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
    }
}

// arith_prim_round!
// prim # big -> Big
// prim # &big -> RefFrom
// &prim # big -> Big
// &prim # &big -> RefFrom
// prim #-> big
// &prim #-> big
// prim #-> big; Round -> Ordering
// &prim #-> big; Round -> Ordering
// struct RefFrom
// big = RefFrom, Round -> Ordering
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
            type Output = $RefFrom<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $RefFrom<'b> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
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
            type Output = $RefFrom<'b>;
            #[inline]
            fn $method(self, rhs: &'b $Big) -> $RefFrom<'b> {
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

// big # mul -> Big
// &big # mul -> Ref
// big #= mul
// big #= mul, Round -> Ordering
// struct Ref
// big = Ref, Round -> Ordering
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: $Mul<'a>) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs,
                }
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

// mul_op_round!
// mul # big -> Big
// mul # &big -> Ref
// mul #-> big
// mul #-> big; Round -> Ordering
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
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
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
    }
}

// mul_op_round!
// mul # big -> Big
// mul # &big -> RefFrom
// mul #-> big
// mul #-> big; Round -> Ordering
// struct RefFrom
// big = RefFrom, Round -> Ordering
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
            type Output = $RefFrom<'a>;
            #[inline]
            fn $method(self, rhs: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs,
                }
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
