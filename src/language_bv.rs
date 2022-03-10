use std::fmt::Debug;
use std::fmt::Display;
use std::str::FromStr;
use std::vec;

use egg::define_language;
use egg::Id;
use egg::Symbol;

use crate::observation_folding_bv::ObsId;

pub const BV_OPS : [str] = [
    "not",
    "and",
    "or",
    "xor",
    "=>",
    "=",
    "ite",

    "concat",
    "bvnot",
    "bvneg",
    "bvand",
    "bvor",
    "bvmul",
    "bvadd",
    "bvudiv",
    "bvurem",
    "bvshl",
    "bvshr",
    "bvult",
];

define_language! {
    pub enum BVLanguage {
        // string variant with no children
        

        // data variants with a single field
        // this field must implement `FromStr` and `Display`
        Bool(bool),
        BV(BVLiteral),
        Obs(ObsId),

        // string variants with an array of child `Id`s (any static size)
        // any type that implements LanguageChildren may be used here

        // Core language operations
        "not" = Not([Id; 1]),
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "xor" = Xor([Id; 2]),
        "=>" = Implies([Id; 2]),
        "=" = Equals([Id; 2]),
        "ite" = ITE([Id; 3]),

        // Bit vector language
        "concat" = BVConcat([Id; 2]),
        "bvnot" = BVNot([Id; 1]),
        "bvneg" = BVNeg([Id; 1]),
        "bvand" = BVAnd([Id; 2]),
        "bvor" = BVOr([Id; 2]),
        "bvmul" = BVMul([Id; 2]),
        "bvadd" = BVAdd([Id; 2]),
        "bvudiv" = BVDiv([Id; 2]),
        "bvurem" = BVRem([Id; 2]),
        "bvshl" = BVShl([Id; 2]),
        "bvshr" = BVShr([Id; 2]),
        "bvult" = BVUlt([Id; 2]),




        // can also do a variable number of children in a boxed slice
        // this will only match if the lengths are the same
        // "list" = List(Box<[Id]>),

        // string variants with a single child `Id`
        // note that this is distinct from `Sub`, even though it has the same
        // string, because it has a different number of children
        // "-"  = Neg(Id),

        
        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Var(Symbol),
        // This is the ultimate fallback, it will parse any operator (as a string)
        // and any number of children.
        // Note that if there were 0 children, the previous branch would have succeeded
        Other(Symbol, Vec<Id>),
        
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BVValue {
    BV(BVLiteral),
    Bool(bool)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct BVLiteral 
{
    length: usize,
    value: Vec<bool>,
}

// trait Nat2Bv : Sized {
//     type Err;
//     fn nat2bv(size: usize, num: &u32) -> Result<Self, Self::Err>;
// }
//
// trait Bv2nat : Sized {
//     type Err;
//     fn bv2nat(bv: &BVLiteral) -> Result<Self, Self::Err>;
// }

fn nat2bv(size: usize, num: u32) -> Result<BVLiteral, String>{
    if size > 32{
        Err(format!("Wrong size: {}", size))
    }else{
        let mut ret_val = BVLiteral{ length: size, value: vec![false; size] };
        ret_val.value = ret_val.value.iter().zip(0..size).map(|(x, i)| (num & (1 << i)) != 0).collect();
        Ok(ret_val)
    }
}

fn bv2nat(bv: &BVLiteral) -> Result<u32, String> {
    if bv.length > 32{
        Err(format!("Bitvector too long: {}", bv.length ))
    }else{
        Ok(bv.value.iter().rev().fold(0, |acc, b| ((acc << 1) | *b as u32)))
    }
}

impl FromStr for BVLiteral {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with("#x") {
            let l = (s.len() - 2) * 4;
            let mut bv : Vec<bool> = Vec::with_capacity(l);
            for (idx, c) in s.chars().rev().enumerate() {
                if idx >= s.len() - 2 { continue;}
                let mut tmp = [0;4];
                let k = u8::from_str_radix(c.encode_utf8(&mut tmp), 16);
                match k {
                    Ok(mut kk) => {
                        for _ in 0..4 {
                            bv.push(kk % 2 == 1); kk /= 2;
                        }
                    }
                    Err(t) => {return Err(format!("Bad BV {} : {}", s, t));}
                }
            }
            return Ok(BVLiteral{length: l, value : bv});

        } else if s.starts_with("#b") {
            let l = s.len() - 2;
            let mut bv : Vec<bool> = Vec::with_capacity(l);
            for (idx, c) in s.chars().rev().enumerate() {
                if idx >= l { continue;}
                if c == '0' {bv.push(false)}
                else if c == '1' {bv.push(true)}
                else {return Err(format!("Bad BV {}", s));}
            }
            return Ok(BVLiteral{length: l, value : bv});

        } else {
            return Err(format!("Bad BV {}", s));
        }
    }
}

impl Display for BVLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#b")?;

        let a = self.value.iter().map(|x| {if *x {'1'} else {'0'}}).rev().collect::<String>();
        write!(f, "{}", a)?;
        Ok(())
    }
}

pub fn test_bvliteral() {
    let a: BVLiteral = BVLiteral::from_str("#b110110").unwrap();
    let b: BVLiteral = BVLiteral::from_str("#x45").unwrap();
    println!("{}", a);
    println!("{}", b);
    assert_eq!(format!("{}", a), "#b110110");
    assert_eq!(format!("{}", b), "#b01000101");
    assert!(BVLiteral::from_str("#xg45").is_err());
    let left = BVLiteral::from_str("#x10").unwrap();
    let right = BVLiteral::from_str("#x03").unwrap();
    println!("{}", left);
    println!("{}", right);
    println!("bvadd: {}", bvadd(&left, &right).unwrap());
    println!("bvudiv: {}", bvudiv(&left, &right).unwrap());
    println!("bvurem: {}", bvurem(&left, &right).unwrap());
    println!("bvshl: {}", bvshl(&left, &right).unwrap());
    println!("bvult: {}", bvult(&left, &right).unwrap());
}


// semantics of BVLanguage
// Given here: https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml

pub fn bvor(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length {
        return None;
    } else {
        Some(BVLiteral{
            length: this.length,
            value: this.value.iter().zip(&that.value).map(|(a,b)| a | b).collect(),
        })
    }
}   

pub fn bvand(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length {
        return None;
    } else {
        Some(BVLiteral{
            length: this.length,
            value: this.value.iter().zip(&that.value).map(|(a,b)| a & b).collect(),
        })
    }
}   

pub fn bvnot(this: &BVLiteral) -> Option<BVLiteral>{
    Some(BVLiteral{
        length: this.length,
        value: this.value.iter().map(|a| !a ).collect(),
    })
}   

pub fn bvconcat(upper: &BVLiteral, lower: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: lower.length + upper.length,
        value: [lower.value.as_slice(), upper.value.as_slice()].concat(),
    })
}   

pub fn bvextract(i:usize, j:usize, this: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: i - j + 1,
        value: this.value[i..j].to_vec(),
    })
} 

pub fn bvneg(this: &BVLiteral) -> Option<BVLiteral>{
    if this.length > 32{
        None
    }else {
        Some(nat2bv(this.length, (2 << (this.length - 1)) - bv2nat(this).ok()?).ok()?)
    }
} 

pub fn bvadd(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length || this.length > 32{
        None
    }else {
        let ret_val = bv2nat(this).ok()?.checked_add(bv2nat(that).ok()?)?;
        Some(nat2bv(this.length, ret_val).ok()?)
    }
} 

pub fn bvmul(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length || this.length > 32{
        None
    }else {
        let ret_val = bv2nat(this).ok()?.checked_mul(bv2nat(that).ok()?)?;
        Some(nat2bv(this.length, ret_val).ok()?)
    }
} 

pub fn bvudiv(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length || this.length > 32{
        None
    }else{
        let ret_val = bv2nat(this).ok()?.checked_div(bv2nat(that).ok()?);
        match ret_val{
            Some(val) => Some(nat2bv(this.length, val).ok()?),
            None => Some(BVLiteral{
                length: this.length,
                value: vec![true; this.length]
            })
        }
    }
} 

pub fn bvurem(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{
    if this.length != that.length || this.length > 32{
        None
    }else{
        let ret_val = bv2nat(this).ok()?.checked_rem(bv2nat(that).ok()?);
        match ret_val{
            Some(val) => Some(nat2bv(this.length, val).ok()?),
            None => Some(this.clone())
        }
    }
} 

pub fn bvshl(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    if this.length != that.length || this.length > 32{
        None
    }else{
        let ret_val = bv2nat(this).ok()? << (bv2nat(that).ok()?);
        Some(nat2bv(this.length, ret_val).ok()?)
    }
} 

pub fn bvlshr(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    if this.length != that.length || this.length > 32{
        None
    }else{
        let ret_val = bv2nat(this).ok()? >> (bv2nat(that).ok()?);
        Some(nat2bv(this.length, ret_val).ok()?)
    }
} 


pub fn bvult(this: &BVLiteral, that: &BVLiteral) -> Option<bool>{
    if this.length != that.length || this.length > 32{
        None
    }else{
        Some(bv2nat(this).ok()? < (bv2nat(that).ok()?))
    }
} 

