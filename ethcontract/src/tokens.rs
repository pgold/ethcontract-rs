//! TODO

use crate::I256;
use arrayvec::ArrayVec;
use ethcontract_common::TransactionHash;
use web3::{
    ethabi::Token,
    types::{Address, U256},
};

/// TODO
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// TODO
    #[error("a")]
    A,
}

/// Simplified output type for single value.
pub trait SingleTokenize {
    /// Converts a `Token` into expected type.
    fn from_token(token: Token) -> Result<Self, Error>
    where
        Self: Sized;
    /// Converts a specified type back into token.
    fn into_token(self) -> Token;
}

impl SingleTokenize for String {
    fn from_token(token: Token) -> Result<Self, Error> {
        match token {
            Token::String(s) => Ok(s),
            other => Err(Error::A),
        }
    }

    fn into_token(self) -> Token {
        Token::String(self)
    }
}

impl SingleTokenize for Address {
    fn from_token(token: Token) -> Result<Self, Error> {
        match token {
            Token::Address(data) => Ok(data),
            other => Err(Error::A),
        }
    }

    fn into_token(self) -> Token {
        Token::Address(self)
    }
}

impl SingleTokenize for TransactionHash {
    fn from_token(token: Token) -> Result<Self, Error> {
        match token {
            Token::FixedBytes(mut s) => {
                if s.len() != 32 {
                    return Err(Error::A);
                }
                let mut data = [0; 32];
                for (idx, val) in s.drain(..).enumerate() {
                    data[idx] = val;
                }
                Ok(data.into())
            }
            other => Err(Error::A),
        }
    }

    fn into_token(self) -> Token {
        Token::FixedBytes(self.as_ref().to_vec())
    }
}

impl SingleTokenize for I256 {
    fn from_token(token: Token) -> Result<Self, Error> {
        // NOTE: U256 accepts both `Int` and `Uint` kind tokens. In fact, all
        //   integer types are expected to accept both.
        Ok(I256::from_raw(U256::from_token(token)?))
    }

    fn into_token(self) -> Token {
        Token::Int(self.into_raw())
    }
}

macro_rules! eth_uint_tokenize {
    ($uint: ident, $name: expr) => {
        impl SingleTokenize for $uint {
            fn from_token(token: Token) -> Result<Self, Error> {
                match token {
                    Token::Int(data) | Token::Uint(data) => {
                        Ok(::std::convert::TryInto::try_into(data).unwrap())
                    }
                    other => Err(Error::A),
                }
            }

            fn into_token(self) -> Token {
                Token::Uint(self.into())
            }
        }
    };
}

eth_uint_tokenize!(U256, "U256");

macro_rules! int_tokenize {
    ($int: ident, $token: ident) => {
        impl SingleTokenize for $int {
            fn from_token(token: Token) -> Result<Self, Error> {
                match token {
                    Token::Int(data) | Token::Uint(data) => Ok(data.low_u128() as _),
                    other => Err(Error::A),
                }
            }

            fn into_token(self) -> Token {
                // this should get optimized away by the compiler for unsigned integers
                #[allow(unused_comparisons)]
                let data = if self < 0 {
                    // NOTE: Rust does sign extension when converting from a
                    // signed integer to an unsigned integer, so:
                    // `-1u8 as u128 == u128::max_value()`
                    U256::from(self as u128) | U256([0, 0, u64::max_value(), u64::max_value()])
                } else {
                    self.into()
                };
                Token::$token(data)
            }
        }
    };
}

int_tokenize!(i8, Int);
int_tokenize!(i16, Int);
int_tokenize!(i32, Int);
int_tokenize!(i64, Int);
int_tokenize!(i128, Int);
int_tokenize!(u8, Uint);
int_tokenize!(u16, Uint);
int_tokenize!(u32, Uint);
int_tokenize!(u64, Uint);
int_tokenize!(u128, Uint);

impl SingleTokenize for bool {
    fn from_token(token: Token) -> Result<Self, Error> {
        match token {
            Token::Bool(data) => Ok(data),
            other => Err(Error::A),
        }
    }

    fn into_token(self) -> Token {
        Token::Bool(self)
    }
}

impl<T> SingleTokenize for Vec<T>
where
    T: SingleTokenize,
{
    fn from_token(token: Token) -> Result<Self, Error> {
        match token {
            Token::FixedArray(tokens) | Token::Array(tokens) => {
                tokens.into_iter().map(SingleTokenize::from_token).collect()
            }
            other => Err(Error::A),
        }
    }

    fn into_token(self) -> Token {
        Token::Array(self.into_iter().map(SingleTokenize::into_token).collect())
    }
}

macro_rules! impl_fixed_types {
    ($num: expr) => {
        impl<T> SingleTokenize for [T; $num]
        where
            T: SingleTokenize,
        {
            fn from_token(token: Token) -> Result<Self, Error>
            where
                Self: Sized,
            {
                let tokens = match token {
                    Token::FixedArray(tokens) => tokens,
                    _ => return Err(Error::A),
                };
                let arr_vec = tokens
                    .into_iter()
                    .map(T::from_token)
                    .collect::<Result<ArrayVec<[T; $num]>, Error>>()?;
                arr_vec.into_inner().map_err(|_| Error::A)
            }

            fn into_token(self) -> Token {
                Token::FixedArray(
                    ArrayVec::from(self)
                        .into_iter()
                        .map(T::into_token)
                        .collect(),
                )
            }
        }
    };
}

impl_fixed_types!(1);
impl_fixed_types!(2);
impl_fixed_types!(3);
impl_fixed_types!(4);
impl_fixed_types!(5);
impl_fixed_types!(6);
impl_fixed_types!(7);
impl_fixed_types!(8);
impl_fixed_types!(9);
impl_fixed_types!(10);
impl_fixed_types!(11);
impl_fixed_types!(12);
impl_fixed_types!(13);
impl_fixed_types!(14);
impl_fixed_types!(15);
impl_fixed_types!(16);
impl_fixed_types!(32);
impl_fixed_types!(64);
impl_fixed_types!(128);
impl_fixed_types!(256);
impl_fixed_types!(512);
impl_fixed_types!(1024);

macro_rules! impl_single_tokenize {
    ($count: expr, $( $ty: ident : $no: tt, )*) => {
        impl<$($ty, )*> SingleTokenize for ($($ty,)*)
        where
            $($ty: SingleTokenize,)*
        {
            fn from_token(token: Token) -> Result<Self, Error>
            {
                let mut tokens = match token {
                    Token::Tuple(tokens) => tokens,
                    _ => return Err(Error::A),
                };
                if tokens.len() != $count {
                    return Err(Error::A);
                }
                #[allow(unused_variables)]
                #[allow(unused_mut)]
                let mut drain = tokens.drain(..);
                Ok(($($ty::from_token(drain.next().unwrap())?,)*))
            }

            fn into_token(self) -> Token {
                Token::Tuple(vec![$(self.$no.into_token(),)*])
            }
        }
    }
}

impl_single_tokenize!(0,);
impl_single_tokenize!(1, A:0, );
impl_single_tokenize!(2, A:0, B:1, );
impl_single_tokenize!(3, A:0, B:1, C:2, );
impl_single_tokenize!(4, A:0, B:1, C:2, D:3, );
impl_single_tokenize!(5, A:0, B:1, C:2, D:3, E:4, );
impl_single_tokenize!(6, A:0, B:1, C:2, D:3, E:4, F:5, );
impl_single_tokenize!(7, A:0, B:1, C:2, D:3, E:4, F:5, G:6, );
impl_single_tokenize!(8, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, );
impl_single_tokenize!(9, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, );
impl_single_tokenize!(10, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, );
impl_single_tokenize!(11, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, );
impl_single_tokenize!(12, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, );
impl_single_tokenize!(13, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, );
impl_single_tokenize!(14, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, );
impl_single_tokenize!(15, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, O:14, );
impl_single_tokenize!(16, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, O:14, P:15, );

/// TODO
pub trait MultiTokenize {
    /// TODO
    fn from_tokens(tokens: Vec<Token>) -> Result<Self, Error>
    where
        Self: Sized;

    /// TODO
    fn into_tokens(self) -> Vec<Token>;
}

macro_rules! impl_multi_tokenize {
  ($count: expr, $( $ty: ident : $no: tt, )*) => {
    impl<$($ty, )*> MultiTokenize for ($($ty,)*) where
      $(
        $ty: SingleTokenize,
      )*
    {
      fn from_tokens(mut tokens: Vec<Token>) -> Result<Self, Error> {
        if tokens.len() != $count {
          return Err(Error::A);
        }
        let mut it = tokens.drain(..);
        Ok(($(
          $ty::from_token(it.next().unwrap())?,
        )*))
      }

      fn into_tokens(self) -> Vec<Token> {
        vec![
          $( self.$no.into_token(), )*
        ]
      }
    }
  }
}

impl_multi_tokenize!(0,);
impl_multi_tokenize!(1, A:0, );
impl_multi_tokenize!(2, A:0, B:1, );
impl_multi_tokenize!(3, A:0, B:1, C:2, );
impl_multi_tokenize!(4, A:0, B:1, C:2, D:3, );
impl_multi_tokenize!(5, A:0, B:1, C:2, D:3, E:4, );
impl_multi_tokenize!(6, A:0, B:1, C:2, D:3, E:4, F:5, );
impl_multi_tokenize!(7, A:0, B:1, C:2, D:3, E:4, F:5, G:6, );
impl_multi_tokenize!(8, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, );
impl_multi_tokenize!(9, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, );
impl_multi_tokenize!(10, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, );
impl_multi_tokenize!(11, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, );
impl_multi_tokenize!(12, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, );
impl_multi_tokenize!(13, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, );
impl_multi_tokenize!(14, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, );
impl_multi_tokenize!(15, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, O:14, );
impl_multi_tokenize!(16, A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7, I:8, J:9, K:10, L:11, M:12, N:13, O:14, P:15, );

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn tokenization() {
        assert_eq!(json!(I256::from(42)), json!("0x2a"));
        assert_eq!(json!(I256::minus_one()), json!(U256::MAX));

        assert_eq!(I256::from(42).into_token(), 42i32.into_token());
        assert_eq!(I256::minus_one().into_token(), Token::Int(U256::MAX),);

        assert_eq!(
            I256::from_token(42i32.into_token()).unwrap(),
            I256::from(42),
        );
        assert_eq!(
            I256::from_token(U256::MAX.into_token()).unwrap(),
            I256::minus_one(),
        );
    }
}
