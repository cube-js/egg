use std::fmt;
use std::str::FromStr;

use crate::*;
use fmt::{Debug, Display, Formatter};
use thiserror::Error;

/// A variable for use in [`Pattern`]s or [`Subst`]s.
///
/// This implements [`FromStr`], and will only parse if it has a
/// leading `?`.
///
/// [`FromStr`]: std::str::FromStr
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(VarInner);

impl Var {
    /// Create a new variable from a u32.
    ///
    /// You can also use special syntax `?#3`, `?#42` to denote a numeric variable.
    /// These avoid some symbol interning, and can also be created manually from
    /// using this function or the `From` impl.
    ///
    /// ```rust
    /// # use egg::*;
    /// assert_eq!(Var::from(12), "?#12".parse().unwrap());
    /// assert_eq!(Var::from_u32(12), "?#12".parse().unwrap());
    /// ```
    pub fn from_u32(num: u32) -> Self {
        Var(VarInner::Num(num))
    }

    /// If this variable was created from a u32, get it back out.
    pub fn as_u32(&self) -> Option<u32> {
        match self.0 {
            VarInner::Num(num) => Some(num),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum VarInner {
    Sym(Symbol),
    Num(u32),
}

#[derive(Debug, Error)]
pub enum VarParseError {
    #[error("pattern variable {0:?} should have a leading question mark")]
    MissingQuestionMark(String),
    #[error("number pattern variable {0:?} was malformed")]
    BadNumber(String),
}

impl FromStr for Var {
    type Err = VarParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use VarParseError::*;

        match s.as_bytes() {
            [b'?', b'#', ..] => s[2..]
                .parse()
                .map(|num| Var(VarInner::Num(num)))
                .map_err(|_| BadNumber(s.to_owned())),
            [b'?', ..] if s.len() > 1 => Ok(Var(VarInner::Sym(Symbol::from(s)))),
            _ => Err(MissingQuestionMark(s.to_owned())),
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            VarInner::Sym(sym) => write!(f, "{}", sym),
            VarInner::Num(num) => write!(f, "?#{}", num),
        }
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            VarInner::Sym(sym) => write!(f, "{:?}", sym),
            VarInner::Num(num) => write!(f, "?#{}", num),
        }
    }
}

impl From<u32> for Var {
    fn from(num: u32) -> Self {
        Var(VarInner::Num(num))
    }
}

/// A substitution mapping [`Var`]s to eclass [`Id`]s.
///
#[derive(Default, Clone)]
pub struct Subst {
    pub(crate) vec: smallvec::SmallVec<[(Var, Id); 3]>,
    /// A place to store arbitrary data associated with this subst
    pub data: Option<std::sync::Arc<dyn std::any::Any + 'static + Send + Sync>>,
}

impl std::hash::Hash for Subst {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.vec.hash(state);
    }
}

impl Ord for Subst {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for Subst {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.vec.partial_cmp(&other.vec)
    }
}

impl Eq for Subst {}

impl PartialEq for Subst {
    fn eq(&self, other: &Self) -> bool {
        self.vec == other.vec
    }
}

impl Subst {
    /// Create a `Subst` with the given initial capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: smallvec::SmallVec::with_capacity(capacity),
            data: None,
        }
    }

    /// Insert something, returning the old `Id` if present.
    pub fn insert(&mut self, var: Var, id: Id) -> Option<Id> {
        for pair in &mut self.vec {
            if pair.0 == var {
                return Some(std::mem::replace(&mut pair.1, id));
            }
        }
        self.vec.push((var, id));
        None
    }

    /// Retrieve a `Var`, returning `None` if not present.
    #[inline(never)]
    pub fn get(&self, var: Var) -> Option<&Id> {
        self.vec
            .iter()
            .find_map(|(v, id)| if *v == var { Some(id) } else { None })
    }

    /// Iterate over the (Var, Id) pairs in this substitution
    pub fn iter(&self) -> impl Iterator<Item = (Var, Id)> + '_ {
        self.vec.iter().copied()
    }
}

impl std::ops::Index<Var> for Subst {
    type Output = Id;

    fn index(&self, var: Var) -> &Self::Output {
        match self.get(var) {
            Some(id) => id,
            None => panic!("Var '{}={}' not found in {:?}", var, var, self),
        }
    }
}

impl std::iter::Extend<(Var, Id)> for Subst {
    fn extend<T: IntoIterator<Item = (Var, Id)>>(&mut self, iter: T) {
        self.vec.extend(iter);
    }
}

impl Debug for Subst {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let len = self.vec.len();
        write!(f, "{{")?;
        for i in 0..len {
            let (var, id) = &self.vec[i];
            write!(f, "{}: {}", var, id)?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn var_parse() {
        assert_eq!(Var::from_str("?a").unwrap().to_string(), "?a");
        assert_eq!(Var::from_str("?abc 123").unwrap().to_string(), "?abc 123");
        assert!(Var::from_str("a").is_err());
        assert!(Var::from_str("a?").is_err());
        assert!(Var::from_str("?").is_err());
        assert!(Var::from_str("?#").is_err());
        assert!(Var::from_str("?#foo").is_err());

        // numeric vars
        assert_eq!(Var::from_str("?#0").unwrap(), Var(VarInner::Num(0)));
        assert_eq!(Var::from_str("?#010").unwrap(), Var(VarInner::Num(10)));
        assert_eq!(
            Var::from_str("?#10").unwrap(),
            Var::from_str("?#0010").unwrap()
        );
        assert_eq!(Var::from_str("?#010").unwrap(), Var(VarInner::Num(10)));
    }
}
