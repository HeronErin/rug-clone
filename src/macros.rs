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

macro_rules! math_op1 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $($param: $T,)*
        ) -> &mut $Big {
            unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                );
            }
            self
        }

        $(#[$attr_ref])*
        pub fn $method_ref(
            &self,
            $($param: $T,)*
        ) -> $Ref {
            $Ref {
                ref_self: self,
                $($param: $param,)*
            }
        }
    }
}

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

macro_rules! math_op1_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $rop: &mut $Big,
            $($param: $T,)*
        ) {
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
        pub fn $method_ref(
            &self,
            $($param: $T,)*
        ) -> $Ref {
            $Ref {
                ref_self: self,
                $($param: $param,)*
            }
        }
    }
}

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

        impl<'a> Assign<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
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

macro_rules! math_op2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $op: &$Big,
            $($param: $T,)*
        ) -> &mut $Big {
            unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                );
            }
            self
        }

        $(#[$attr_ref])*
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a $Big,
            $($param: $T,)*
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op: $op,
                $($param: $param,)*
            }
        }
    }
}

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

macro_rules! math_op2_2 {
    {
        $Big:ty;
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $op: &mut $Big,
            $($param: $T,)*
        ) {
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
        pub fn $method_ref<'a>(
            &'a self,
            $op: &'a $Big,
            $($param: $T,)*
        ) -> $Ref<'a> {
            $Ref {
                ref_self: self,
                $op: $op,
                $($param: $param,)*
            }
        }
    }
}

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

        impl<'a> Assign<$Ref<'a>> for (&'a mut $Big, &'a mut $Big) {
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

macro_rules! from_borrow {
    { $Src:ty => $Dst:ty} => {
        impl<'a> From<$Src> for $Dst {
            fn from(t: $Src) -> $Dst {
                let mut ret = <$Dst>::new();
                ret.assign(t);
                ret
            }
        }
    }
}

macro_rules! from {
    { $Src:ty => $Dst:ty } => {
        impl From<$Src> for $Dst {
            fn from(t: $Src) -> $Dst {
                let mut ret = <$Dst>::new();
                ret.assign(t);
                ret
            }
        }
    }
}

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
            fn $method(mut self) -> $Big {
                self.$method_assign();
                self
            }
        }

        impl $ImpAssign for $Big {
            fn $method_assign(&mut self) {
                unsafe {
                    $func(self.inner_mut(), self.inner());
                }
            }
        }

        impl<'a> $Imp for &'a $Big {
            type Output = $Ref<'a>;
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
            fn assign(&mut self, rhs: $Ref) {
                unsafe {
                    $func(self.inner_mut(), rhs.op.inner());
                }
            }
        }
    }
}

macro_rules! arith_binary {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $Ref:ident
    } => {
        impl $Imp<$Big> for $Big {
            type Output = $Big;
            fn $method(self, op: $Big) -> $Big {
                self.$method(&op)
            }
        }

        impl<'a> $Imp<&'a $Big> for $Big {
            type Output = $Big;
            fn $method(mut self, op: &'a $Big) -> $Big {
                $ImpAssign::<&'a $Big>::$method_assign(&mut self, op);
                self
            }
        }

        impl $ImpAssign<$Big> for $Big {
            fn $method_assign(&mut self, op: $Big) {
                self.$method_assign(&op);
            }
        }

        impl<'a> $ImpAssign<&'a $Big> for $Big {
            fn $method_assign(&mut self, op: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), op.inner());
                }
            }
        }

        impl<'a> $Imp<&'a $Big> for &'a $Big {
            type Output = $Ref<'a>;
            fn $method(self, rhs: &'a $Big) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs: rhs,
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
            fn assign(&mut self, rhs: $Ref) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.inner());
                }
            }
        }
    }
}

macro_rules! arith_noncommut {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFromAssign:ident $method_from_assign:ident;
        $Ref:ident
    } => {
        arith_binary! {
            $Big; $func; $Imp $method; $ImpAssign $method_assign; $Ref
        }

        impl $ImpFromAssign<$Big> for $Big {
            fn $method_from_assign(&mut self, lhs: $Big) {
                self.$method_from_assign(&lhs);
            }
        }

        impl<'a> $ImpFromAssign<&'a $Big> for $Big {
            fn $method_from_assign(&mut self, lhs: &'a $Big) {
                unsafe {
                    $func(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }
    }
}

macro_rules! arith_prim {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    }=> {
        impl $Imp<$T> for $Big {
            type Output = $Big;
            fn $method(mut self, op: $T) -> $Big {
                self.$method_assign(op);
                self
            }
        }

        impl $ImpAssign<$T> for $Big {
            fn $method_assign(&mut self, op: $T) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), op.into());
                }
            }
        }

        impl<'a> $Imp<$T> for &'a $Big {
            type Output = $Ref<'a>;
            fn $method(self, op: $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs: op,
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
            fn assign(&mut self, rhs: $Ref) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.into());
                }
            }
        }
    }
}

macro_rules! arith_prim_noncommut {
    {
        $Big:ty;
        $func:path;
        $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpFromAssign:ident $method_from_assign:ident;
        $T:ty;
        $Ref:ident $RefFrom:ident
    } => {
        arith_prim! {
            $Big; $func; $Imp $method; $ImpAssign $method_assign; $T; $Ref
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            fn $method(self, mut op: $Big) -> $Big {
                op.$method_from_assign(self);
                op
            }
        }

        impl $ImpFromAssign<$T> for $Big {
            fn $method_from_assign(&mut self, lhs: $T) {
                unsafe {
                    $func_from(self.inner_mut(), lhs.into(), self.inner());
                }
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $RefFrom<'a>;
            fn $method(self, op: &'a $Big) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs: op,
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
            fn assign(&mut self, rhs: $RefFrom) {
                unsafe {
                    $func_from(self.inner_mut(),
                               rhs.lhs.into(),
                               rhs.rhs.inner());
                }
            }
        }
    }
}

macro_rules! arith_prim_commut {
    {
        $Big:ty;
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim! {
            $Big; $func; $Imp $method; $ImpAssign $method_assign; $T; $Ref
        }

        impl $Imp<$Big> for $T {
            type Output = $Big;
            fn $method(self, op: $Big) -> $Big {
                op.$method(self)
            }
        }

        impl<'a> $Imp<&'a $Big> for $T {
            type Output = $Ref<'a>;
            fn $method(self, op: &'a $Big) -> $Ref<'a> {
                op.$method(self)
            }
        }
    }
}
