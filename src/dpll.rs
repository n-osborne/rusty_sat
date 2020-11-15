use crate::dpll::SATISFIABILITY::{SAT, UNSAT};

#[derive(PartialEq)]
#[derive(Debug)]
pub enum SATISFIABILITY {
    SAT,
    UNSAT,
}


#[derive(Clone)]
pub struct  Formula {
    pub cnf: Vec<Vec<i32>>,
    pub max_lit: i32,
}

impl Formula {
    pub fn new(cnf: Vec<Vec<i32>>) -> Formula {
        let mut max_lit = 0;
        for c in cnf.iter() {
            if let Some(m) = c.iter().map(|i| i.abs()).max() {
                max_lit = max_lit.max(m.abs());
            }
        }
        Formula { cnf, max_lit }
    }
    pub fn is_empty(&self) -> bool {
        self.cnf.is_empty()
    }
    pub fn contains_empty_clause(&self) -> bool {
        self.cnf.iter().any(|c| c.is_empty())
    }
    pub fn mk_lit_true(&mut self, lit: i32) {
        let mut i:usize = 0;
        while i < self.cnf.len() {
            if self.cnf[i].contains(&lit) {
                self.cnf.remove(i);
            } else if self.cnf[i].contains(&-lit) {
                self.cnf[i].retain(|l| l != &-lit);
                i += 1;
            } else {
                i += 1;
            }
        }
    }
    pub fn mk_lit_false(&mut self, lit: i32) {
        self.mk_lit_true(-lit);
    }
    pub fn find_unit(&self) -> Option<usize> {
        self.cnf.iter().position(|c| c.len() == 1)
    }
    pub fn is_pure(&self, i: i32) -> bool {
        let mut pos = false;
        let mut neg = false;
        for c in self.cnf.iter() {
            for l in c.iter() {
                if l.abs() == i.abs() {
                    if l >= &0 {
                        pos = true;
                    } else {
                        neg = true;
                    }
                }
            }
        }
        pos ^ neg
    }
    pub fn find_pure(&self) -> Option<i32> {
        (0..self.max_lit+1).find(|x| self.is_pure(*x))
    }
    pub fn recursive_dpll(&mut self) -> SATISFIABILITY {
        if self.is_empty() {
            SAT
        } else if self.contains_empty_clause() {
            UNSAT
        } else if let Some(lit) = self.find_pure() {
            self.mk_lit_true(lit);
            self.recursive_dpll()
        } else if let Some(u) = self.find_unit() {
            let lit = self.cnf[u][0];
            self.mk_lit_true(lit);
            self.recursive_dpll()
        } else {
            let lit = self.cnf[0][0];
            let mut f: Formula = self.clone();
            f.mk_lit_true(lit);
            if f.recursive_dpll() == SAT {
                SAT
            } else {
                self.mk_lit_false(lit);
                self.recursive_dpll()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::dpll::Formula;
    use crate::dpll::SATISFIABILITY::*;

    fn cnf() -> Formula {
        Formula::new(vec![vec![1,2,3],vec![-3,4,5]])
    }
    #[test]
    fn test_is_empty() {
        assert!(Formula::new(vec![]).is_empty());
        assert!(!cnf().is_empty());
    }
    #[test]
    fn test_contains_empty_clause() {
        assert!(Formula::new(vec![vec![1,2],vec![]]).contains_empty_clause());
        assert!(!cnf().contains_empty_clause());
    }
    #[test]
    fn test_find_unit() {
        assert_eq!(cnf().find_unit(), None);
        assert_eq!(Formula::new(vec![vec![1,2],vec![3]]).find_unit(), Some(1));
    }
    #[test]
    fn test_is_pure() {
        assert!(cnf().is_pure(1));
        assert!(!cnf().is_pure(3));
    }
    #[test]
    fn test_find_pure_some() {
        let f = Formula::new(vec![vec![1,2],vec![-1,2]]);
        assert_eq!(f.find_pure(), Some(2));
    }
    #[test]
    fn test_find_pure_none() {
        let f = Formula::new(vec![vec![1,2],vec![-1,-2]]);
        assert!(f.find_pure().is_none());
    }
    #[test]
    fn test_mk_lit_true() {
        let mut f = Formula::new(vec![vec![1,2],vec![3,4]]);
        f.mk_lit_true(2);
        assert_eq!(f.cnf, vec![vec![3, 4]]);
        f.mk_lit_true(-3);
        assert_eq!(f.cnf, vec![vec![4]]);
    }
    #[test]
    fn test_mk_lit_false() {
        let mut f = Formula::new(vec![vec![1,2],vec![3,4]]);
        f.mk_lit_false(1);
        assert_eq!(f.cnf, vec![vec![2], vec![3, 4]]);
        f.mk_lit_false(-4);
        assert_eq!(f.cnf, vec![vec![2]]);
    }
    #[test]
    fn test_dlpp() {
        let mut f = Formula::new(vec![vec![1,2]]);
        assert_eq!(f.recursive_dpll(), SAT);
        let mut f = Formula::new(vec![vec![1,2],vec![-1,2]]);
        assert_eq!(f.recursive_dpll(), SAT);
        let mut f = Formula::new(vec![vec![1],vec![-1]]);
        assert_eq!(f.recursive_dpll(), UNSAT);
    }
}