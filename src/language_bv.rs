use std::fmt::Debug;
use std::fmt::Display;
use std::str::FromStr;

use egg::define_language;
use egg::Id;
use egg::Symbol;

define_language! {
    enum BVLanguage {
        // string variant with no children
        

        // data variants with a single field
        // this field must implement `FromStr` and `Display`
        Bool(bool),
        BV(BVLiteral),


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
        //TODO: need bvextract ((_ extract i j) s)




        // can also do a variable number of children in a boxed slice
        // this will only match if the lengths are the same
        // "list" = List(Box<[Id]>),

        // string variants with a single child `Id`
        // note that this is distinct from `Sub`, even though it has the same
        // string, because it has a different number of children
        // "-"  = Neg(Id),

        
        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last
        Symbol(Symbol),
        // This is the ultimate fallback, it will parse any operator (as a string)
        // and any number of children.
        // Note that if there were 0 children, the previous branch would have succeeded
        Other(Symbol, Vec<Id>),
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct BVLiteral 
{
    length: usize,
    value: Vec<bool>,
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
        length: 0,
        value: vec![],
    })
} 

pub fn bvneg(this: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvadd(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvmul(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvudiv(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvurem(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvshl(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 

pub fn bvlshr(this: &BVLiteral, that: &BVLiteral) -> Option<BVLiteral>{

    Some(BVLiteral{
        length: 0,
        value: vec![],
    })
} 


pub fn bvult(this: &BVLiteral, that: &BVLiteral) -> Option<bool>{

    Some(true)
} 

