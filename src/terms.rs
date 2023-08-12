// macro_rules! myprint{
//     ($($elem: expr),+ ) => {
//         println!(concat!($(concat!(stringify!($elem), " = {:?}")),+), $($elem),+);
//     };
// }

use super::myerr;
use super::BoxRes;
use super::ErrCode;
use super::MyError;
use std::collections::HashMap;

use self::TermEntry::*;
use self::TypeEntry::*;

#[derive(Copy, Clone, PartialEq)]
pub struct Ty {
    data: u32,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Tm {
    data: u32,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Thm {
    data: u32,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum TmOrThm {
    Tm(Tm),
    Thm(Thm),
}

pub enum TermEntry {
    Theorem(Tm), // Theorem of a bool
    ForAll(Ty),
    Lambda(Tm, Tm), // var,out
    FunAp(Tm, Tm),  // fun,inp
    Pair(Tm, Tm),
    Fst(Tm),
    Snd(Tm),
    Var,
    Def(Tm), // or Def?
}

pub enum TypeEntry {
    Pairs(Ty, Ty),
    Pred(Ty),
    Bool,
    Set,
    TheoremType, // should only exist once
}

pub struct Terms {
    // every term entry has a type
    pub tms: Vec<(TermEntry, Ty)>,
    pub tys: Vec<TypeEntry>,
}

struct MatchHelper {
    loc_defs_l: HashMap<Tm, Tm>,
    loc_defs_r: HashMap<Tm, Tm>,
    old_defs: Vec<(Tm, bool, Tm)>,
    trans_l2r: HashMap<Tm, Tm>,
    trans_r2l: HashMap<Tm, Tm>,
    swapped: bool,
    fst_snd_stack: Vec<bool>, // true means fst
                              // should translations be symmetric? not necessary
}

impl Ty {
    fn new(x: usize) -> Ty {
        Ty { data: (x as u32) }
    }

    fn to_usize(&self) -> usize {
        self.data as usize
    }
}

impl Tm {
    fn new(x: usize) -> Tm {
        Tm { data: x as u32 }
    }

    fn to_usize(&self) -> usize {
        self.data as usize
    }
}

impl Thm {
    fn from_tm(tm: Tm) -> Thm {
        Thm { data: tm.data }
    }

    fn to_usize(&self) -> usize {
        self.data as usize
    }
}

impl TmOrThm {
    pub fn from_tm(tm: Tm) -> TmOrThm {
        TmOrThm::Tm(tm)
    }

    pub fn from_thm(thm: Thm) -> TmOrThm {
        TmOrThm::Thm(thm)
    }

    pub fn get_tm(&self) -> BoxRes<&Tm> {
        match self {
            TmOrThm::Tm(a) => Ok(a),
            TmOrThm::Thm(_) => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    pub fn get_thm(&self) -> BoxRes<&Thm> {
        match self {
            TmOrThm::Tm(_) => Err(MyError::new(ErrCode::Impossible)),
            TmOrThm::Thm(a) => Ok(a),
        }
    }

    fn to_usize(&self) -> usize {
        match self {
            TmOrThm::Tm(a) => a.to_usize(),
            TmOrThm::Thm(a) => a.to_usize(),
        }
    }
}

impl MatchHelper {
    pub fn new() -> MatchHelper {
        MatchHelper {
            loc_defs_l: HashMap::new(),
            loc_defs_r: HashMap::new(),
            old_defs: Vec::new(),
            trans_l2r: HashMap::new(),
            trans_r2l: HashMap::new(),
            swapped: false,
            fst_snd_stack: Vec::new(),
        }
    }

    fn get_map(&self, l: bool) -> &HashMap<Tm, Tm> {
        if l ^ self.swapped {
            &self.loc_defs_l
        } else {
            &self.loc_defs_r
        }
    }

    fn get_mut_map(&mut self, l: bool) -> &mut HashMap<Tm, Tm> {
        if l ^ self.swapped {
            &mut self.loc_defs_l
        } else {
            &mut self.loc_defs_r
        }
    }

    //   fn swap(&mut self) {
    //     self.swapped = !self.swapped;
    //   }

    fn get_local_def(&self, tm: Tm, l: bool) -> BoxRes<Tm> {
        //     let opt:Option<&Tm> =
        let ld = self.get_map(l);
        match ld.get(&tm) {
            None => Err(MyError::new(ErrCode::Impossible)),
            Some(x) => Ok(*x),
        }
    }

    fn has_def(&self, tm: Tm, l: bool) -> bool {
        let ld = self.get_map(l);
        ld.contains_key(&tm)
    }

    fn is_trans(&self, tm1: Tm, tm2: Tm) -> BoxRes<bool> {
        // check if tm1 and tm2 correspond
        //   to each other in a translation

        let (tm_a, tm_b): (Tm, Tm) = if self.swapped { (tm2, tm1) } else { (tm1, tm2) };
        match self.trans_l2r.get(&tm_a) {
            Some(tm_x) => {
                if *tm_x == tm_b {
                    let tm_y: &Tm = myerr::opt2imposs(self.trans_r2l.get(&tm_b))?;
                    myerr::expected(true, *tm_y == tm_a)?;
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            // the has_def already respects swapped, so we need to
            // use tm1,tm2 again when calling it
            None => Ok(tm_a == tm_b && !self.has_def(tm1, true) && !self.has_def(tm2, false)),
        }
    }

    fn has_trans(&self, tm: Tm, l: bool) -> bool {
        if l ^ self.swapped {
            self.trans_l2r.contains_key(&tm)
        } else {
            self.trans_r2l.contains_key(&tm)
        }
    }

    fn add_def(&mut self, tm1: Tm, tm2: Tm, l: bool) -> BoxRes<bool> {
        // returns true if successful
        // returns false if problems with translations

        if self.has_trans(tm1, l) {
            // check for collisions with trans
            return Ok(false);
        }
        let ld = self.get_mut_map(l);
        if let Some(old) = ld.insert(tm1, tm2) {
            self.old_defs.push((tm1, l ^ self.swapped, old));
        }
        Ok(true)
    }
    // - if there are collisions with trans and loc_defs, return false
    //    - translations can only happen inside lambdas,
    //      and lambdas are not crucial

    fn remove_def(&mut self, tm1: Tm, tm2: Tm, l: bool) -> BoxRes<()> {
        let old_tm2: Option<Tm> = if let Some((o_tm1, o_l, o_tm2)) = self.old_defs.last() {
            if o_tm1 == &tm1 && *o_l == l ^ self.swapped {
                Some(*o_tm2)
            //         let y = ld.insert(tm1,*o_tm2);
            } else {
                None
            }
        } else {
            None
        };
        if let Some(_) = old_tm2 {
            self.old_defs.pop();
        }

        let ld = self.get_mut_map(l);
        let res = match old_tm2 {
            Some(x) => ld.insert(tm1, x),
            None => ld.remove(&tm1),
        };

        match res {
            Some(x) if x == tm2 => Ok(()),
            _ => Err(MyError::new(ErrCode::Impossible)),
        }?;
        Ok(())
    }

    fn add_translation(&mut self, tm1: Tm, tm2: Tm) -> BoxRes<bool> {
        let has_1 = self.has_trans(tm1, true);
        let has_2 = self.has_trans(tm2, false);
        if has_1 || has_2 {
            //       return if has_1 && has_2 {
            //         Ok(false)
            //       } else {
            //         return Err(MyError::new(ErrCode::Impossible))
            //       };
            return Ok(false);
        }
        let (tm_a, tm_b): (Tm, Tm) = if self.swapped { (tm2, tm1) } else { (tm1, tm2) };
        match (
            self.trans_l2r.insert(tm_a, tm_b),
            self.trans_r2l.insert(tm_b, tm_a),
        ) {
            (None, None) => Ok(true),
            _ => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    fn remove_translation(&mut self, tm1: Tm, tm2: Tm) -> BoxRes<()> {
        let (tm_a, tm_b): (Tm, Tm) = if self.swapped { (tm2, tm1) } else { (tm1, tm2) };
        match (self.trans_l2r.remove(&tm_a), self.trans_r2l.remove(&tm_b)) {
            (Some(x1), Some(x2)) if x1 == tm_b && x2 == tm_a => Ok(()),
            _ => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    fn has_no_terms(&self) -> bool {
        let b = self.loc_defs_r.is_empty();
        let b = b && self.loc_defs_l.is_empty();
        let b = b && self.trans_l2r.is_empty();
        b && self.trans_r2l.is_empty()
    }

    fn fst_snd_stack_is_empty(&self) -> bool {
        self.fst_snd_stack.is_empty()
    }

    fn add_to_stack(&mut self, x: bool) {
        self.fst_snd_stack.push(x)
    }

    fn pop_stack(&mut self) -> BoxRes<bool> {
        let b = myerr::opt2imposs(self.fst_snd_stack.pop())?;
        Ok(b)
    }

    fn confirm_stack_size(&self, l: usize) -> BoxRes<()> {
        if l == self.fst_snd_stack.len() {
            Ok(())
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }
}

impl Terms {
    pub fn new() -> Terms {
        let mut t = Terms {
            tms: Vec::new(),
            tys: Vec::new(),
        };
        t.init();
        t
    }

    fn init(&mut self) {
        // stacks should be empty
        // init `bool`, `set` types
        self.tys.push(TypeEntry::TheoremType);
        self.tys.push(TypeEntry::Bool);
        self.tys.push(TypeEntry::Set);
        // init `imp` term, first construct the term
        let bool_ty: Ty = self.bool_type();
        let pair_ty: Ty = self.new_pair_type(bool_ty, bool_ty);
        let imp_ty: Ty = self.new_pred_type(pair_ty);
        // init imp as first element
        self.tms.push((TermEntry::Var, imp_ty));
    }

    // TODO: is this needed in the end?
    pub fn is_thm(&self, tmthm: TmOrThm) -> BoxRes<bool> {
        let (tm2, ty) = self.get_tmorthm_entry(tmthm)?;
        if let TermEntry::Theorem(_) = tm2 {
            Ok(self.is_theorem_type(*ty))
        } else {
            Ok(false)
        }
    }

    pub fn is_def(&self, tm: Tm) -> BoxRes<bool> {
        let (tm2, _) = self.get_term_entry(tm)?;
        if let TermEntry::Def(_) = tm2 {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub fn is_var(&self, tm: Tm) -> BoxRes<bool> {
        let (tm2, _) = self.get_term_entry(tm)?;
        if let TermEntry::Var = tm2 {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn new_entry(&mut self, tm_entry: TermEntry, ty: Ty) -> Tm {
        let s = self.tms.len();
        self.tms.push((tm_entry, ty));
        Tm::new(s)
    }

    fn new_type_entry(&mut self, ty_entry: TypeEntry) -> Ty {
        let s = self.tys.len();
        self.tys.push(ty_entry);
        Ty::new(s)
    }

    pub fn new_def(&mut self, tm: Tm) -> BoxRes<Tm> {
        let ty: Ty = self.get_type(tm)?;
        Ok(self.new_entry(Def(tm), ty))
    }

    pub fn new_var(&mut self, ty: Ty) -> Tm {
        self.new_entry(Var, ty)
    }

    pub fn get_type(&self, tm: Tm) -> BoxRes<Ty> {
        let (_, ty) = self.get_term_entry(tm)?;
        Ok(*ty)
        //     if let Some((_, ty)) = self.tms.get(tm) {
        //       Ok(*ty)
        //     } else {
        //       Err(MyError::new(ErrCode::Impossible))
        //     }
    }

    pub fn new_pair_type(&mut self, ty1: Ty, ty2: Ty) -> Ty {
        self.new_type_entry(TypeEntry::Pairs(ty1, ty2))
    }

    pub fn new_pred_type(&mut self, of: Ty) -> Ty {
        self.new_type_entry(TypeEntry::Pred(of))
    }

    pub fn new_pair(&mut self, tm1: Tm, tm2: Tm) -> BoxRes<Tm> {
        let ty1: Ty = self.get_type(tm1)?;
        let ty2: Ty = self.get_type(tm2)?;
        let p_ty: Ty = self.new_pair_type(ty1, ty2);
        Ok(self.new_entry(Pair(tm1, tm2), p_ty))
    }

    pub fn new_fst(&mut self, pair_tm: Tm) -> BoxRes<Tm> {
        let p_ty: Ty = self.get_type(pair_tm)?;
        let (ty, _) = self.destruct_pair_type(p_ty)?;
        Ok(self.new_entry(Fst(pair_tm), ty))
    }

    pub fn new_snd(&mut self, pair_tm: Tm) -> BoxRes<Tm> {
        let p_ty: Ty = self.get_type(pair_tm)?;
        let (_, ty) = self.destruct_pair_type(p_ty)?;
        Ok(self.new_entry(Snd(pair_tm), ty))
    }

    fn destruct_pair_type(&self, p: Ty) -> BoxRes<(Ty, Ty)> {
        let x = self.get_type_entry(p)?;
        if let TypeEntry::Pairs(ty1, ty2) = x {
            Ok((*ty1, *ty2))
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn destruct_pred_type(&self, p: Ty) -> BoxRes<Ty> {
        let x = self.get_type_entry(p)?;
        if let TypeEntry::Pred(ty) = x {
            Ok(*ty)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn destruct_def(&self, tm: Tm) -> BoxRes<Tm> {
        let (x, _) = self.get_term_entry(tm)?;
        if let Def(tm2) = x {
            Ok(*tm2)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn new_lambda(&mut self, var: Tm, out: Tm) -> BoxRes<Tm> {
        // assume that var is of type `x`,
        // assume that var already exists,
        // assume that var is a local variable only for term out
        let var_ty: Ty = self.get_type(var)?;
        let pred_ty: Ty = self.new_pred_type(var_ty);
        let lambda = self.new_entry(Lambda(var, out), pred_ty);

        if let Ok(true) = self.is_bool(out) {
            Ok(lambda)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn new_forall(&mut self, ty: Ty) -> Tm {
        let pred_ty = self.new_pred_type(ty);
        let pred_2_ty = self.new_pred_type(pred_ty);
        self.new_entry(ForAll(ty), pred_2_ty)
    }

    pub fn funap_type_check(&self, fun: Tm, inp: Tm) -> BoxRes<bool> {
        // fun is of type `x`, inp is of type `y`
        // returns true if x matches with `pred y`
        let fun_ty = self.get_type(fun)?;
        let inp_ty = self.get_type(inp)?;
        if let Ok(x) = self.destruct_pred_type(fun_ty) {
            self.match_types(inp_ty, x)
        } else {
            Ok(false)
        }
    }

    pub fn get_type_entry(&self, ty: Ty) -> BoxRes<&TypeEntry> {
        return myerr::opt2imposs(self.tys.get(ty.to_usize()));
    }

    pub fn get_term_entry(&self, tm: Tm) -> BoxRes<&(TermEntry, Ty)> {
        return myerr::opt2imposs(self.tms.get(tm.to_usize()));
    }

    fn get_tmorthm_entry(&self, tmthm: TmOrThm) -> BoxRes<&(TermEntry, Ty)> {
        return myerr::opt2imposs(self.tms.get(tmthm.to_usize()));
    }

    pub fn is_pred_type(&self, ty: Ty) -> BoxRes<bool> {
        let x = self.get_type_entry(ty)?;
        Ok(match x {
            TypeEntry::Pred(_) => true,
            _ => false,
        })
    }

    pub fn is_pair(&self, tm: Tm) -> BoxRes<bool> {
        // checks if the type of tm has a pair structure
        let ty: Ty = self.get_type(tm)?;
        let x = self.get_type_entry(ty)?;
        Ok(match x {
            TypeEntry::Pairs(_, _) => true,
            _ => false,
        })
    }

    pub fn is_bool(&self, tm: Tm) -> BoxRes<bool> {
        let ty: Ty = self.get_type(tm)?;
        self.match_types(ty, self.bool_type())
    }

    fn is_theorem_type(&self, ty: Ty) -> bool {
        ty == self.theorem_type()
    }

    pub fn bool_type(&self) -> Ty {
        // returns bool type
        Ty::new(1)
    }

    pub fn set_type(&self) -> Ty {
        // returns set type
        Ty::new(2)
    }

    fn theorem_type(&self) -> Ty {
        // returns the type of theorems
        Ty::new(0)
    }

    pub fn imp_term(&self) -> Tm {
        // returns `imp` term
        Tm::new(0)
    }

    pub fn new_funap(&mut self, fun: Tm, inp: Tm) -> BoxRes<Tm> {
        // checks if types are compatible
        if self.funap_type_check(fun, inp)? {
            let bool_ty: Ty = self.bool_type();
            Ok(self.new_entry(FunAp(fun, inp), bool_ty))
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn thm2bool(&self, thm: Thm) -> BoxRes<Tm> {
        // let (x,_) = self.get_term_entry(thm)?;
        let (x, _) = myerr::opt2imposs(self.tms.get(thm.to_usize()))?;
        if let Theorem(tm) = x {
            Ok(*tm)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn bool2thm(&mut self, tm: Tm) -> BoxRes<Thm> {
        let thm_ty: Ty = self.theorem_type();
        if let Ok(true) = self.is_bool(tm) {
            Ok(Thm::from_tm(self.new_entry(Theorem(tm), thm_ty)))
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn var2thm(&mut self, thm: Thm, var: Tm) -> BoxRes<Thm> {
        // add forall, lambda

        let ty: Ty = self.get_type(var)?;
        let forall: Tm = self.new_forall(ty);
        let thmtm: Tm = self.thm2bool(thm)?;
        let lambda: Tm = self.new_lambda(var, thmtm)?;
        let funap: Tm = self.new_funap(forall, lambda)?;
        self.bool2thm(funap)
    }

    pub fn asm2thm(&mut self, thm: Thm, asm: Thm) -> BoxRes<Thm> {
        let thm_tm: Tm = self.thm2bool(thm)?;
        let asm_tm: Tm = self.thm2bool(asm)?;
        let pair: Tm = self.new_pair(asm_tm, thm_tm)?;
        let imp: Tm = self.imp_term();
        let funap: Tm = self.new_funap(imp, pair)?;
        self.bool2thm(funap)
    }

    pub fn def2thm(&mut self, thm: Thm, def: Tm) -> BoxRes<Thm> {
        // use funap, lambda, to create a theorem
        // def was created by new_def
        // also modifies def entry from link to Var
        let thm_tm: Tm = self.thm2bool(thm)?;
        let inp: Tm = self.destruct_def(def)?;
        let inp_ty = self.get_type(inp)?;

        // change link to var for def
        let entry = myerr::opt2imposs(self.tms.get_mut(def.to_usize()))?;
        *entry = (Var, inp_ty);

        // create lambda and funap
        let lambda = self.new_lambda(def, thm_tm)?;
        let funap: Tm = self.new_funap(lambda, inp)?;
        self.bool2thm(funap)
    }

    fn destruct_pair(&self, tm: Tm) -> Option<(Tm, Tm)> {
        if let Some((Pair(x, y), _)) = self.tms.get(tm.to_usize()) {
            Some((*x, *y))
        } else {
            None
        }
    }

    fn destruct_lambda(&self, tm: Tm) -> Option<(Tm, Tm)> {
        if let Some((Lambda(x, y), _)) = self.tms.get(tm.to_usize()) {
            Some((*x, *y))
        } else {
            None
        }
    }

    fn destruct_funap(&self, tm: Tm) -> Option<(Tm, Tm)> {
        // returns None if not a funap
        if let Some((FunAp(x, y), _)) = self.tms.get(tm.to_usize()) {
            Some((*x, *y))
        } else {
            None
        }
    }

    pub fn destruct_imp_thm(&self, thm: Thm) -> BoxRes<(Tm, Tm)> {
        // returns ImpMatch error when not an `. imp pr p q`

        let thm_tm: Tm = self.thm2bool(thm)?;
        match self.destruct_funap(thm_tm) {
            None => Err(MyError::new(ErrCode::ImpMatch)),
            Some((fun, inp)) => {
                // note: matching of functions is not too advanced
                // cannot match with `\ x pairs bool bool . imp x` here
                //         if !self.match_terms(fun, self.imp_term())? {

                // only check simple equality, nothing too advanced
                if fun != self.imp_term() {
                    return Err(MyError::new(ErrCode::ImpMatch));
                }
                match self.destruct_pair(inp) {
                    None => Err(MyError::new(ErrCode::ImpMatch)),
                    Some(pq) => Ok(pq),
                }
            }
        }
    }

    pub fn destruct_forall_thm(&self, thm: Thm) -> BoxRes<(Tm, Ty)> {
        // also destructs the funap
        // return tm should be of type `pred ty`
        // returns ForallMatch error if not matchable
        // `. ! tm` -> tm

        let thm_tm: Tm = self.thm2bool(thm)?;
        if let Some((fun, inp)) = self.destruct_funap(thm_tm) {
            // let (fun_entry, _) = myerr::opt2imposs(self.tms.get(fun))?;
            let (fun_entry, _) = self.get_term_entry(fun)?;
            match fun_entry {
                ForAll(ty) => Ok((inp, *ty)),
                _ => Err(MyError::new(ErrCode::ForallMatch)),
            }
        } else {
            Err(MyError::new(ErrCode::ForallMatch))
        }
    }

    pub fn match_thm_term(&self, thm: Thm, tm: Tm) -> BoxRes<bool> {
        // check if the theorem matches with the term
        //     if !self.is_thm(TmOrThm::new(thm))? {
        //       Err(MyError::new(ErrCode::Impossible))
        //     } else
        if self.is_bool(tm)? {
            let thm_tm = self.thm2bool(thm)?;
            self.match_terms(thm_tm, tm)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn match_types(&self, ty1: Ty, ty2: Ty) -> BoxRes<bool> {
        // checks if types are equal
        if ty1 == ty2 {
            return Ok(true);
        }
        let x1 = self.get_type_entry(ty1)?;
        let x2 = self.get_type_entry(ty2)?;

        match (x1, x2) {
            (Bool, Bool) => Ok(true),
            (Set, Set) => Ok(true),
            (Pred(y1), Pred(y2)) => self.match_types(*y1, *y2),
            (Pairs(y1, z1), Pairs(y2, z2)) => {
                if self.match_types(*y1, *y2)? {
                    self.match_types(*z1, *z2)
                } else {
                    Ok(false)
                }
            }
            (TheoremType, _) => Err(MyError::new(ErrCode::Impossible)),
            (_, TheoremType) => Err(MyError::new(ErrCode::Impossible)),
            (_, _) => Ok(false),
        }
    }

    fn match_terms(&self, tm1: Tm, tm2: Tm) -> BoxRes<bool> {
        // check if the terms match.
        // this function does not call itself

        // criteria if two terms match:
        //  - reduce all defs
        //  - reduce all . \ constructs
        //  - replace all pair variables with components
        //    `a` -> `pr fst a snd a`
        //  - reduce `fst pr a b` -> `a`, `snd pr a b` -> b
        //  - then match
        //    - translate local variables

        let mut mh = MatchHelper::new();
        let ty1: Ty = self.get_type(tm1)?;
        let ty2: Ty = self.get_type(tm2)?;
        if !self.match_types(ty1, ty2)? {
            return Ok(false);
        }
        let res = self.match_internal(tm1, tm2, &mut mh)?;
        mh.confirm_stack_size(0)?;
        if !mh.has_no_terms() {
            return Err(MyError::new(ErrCode::Impossible));
        }
        Ok(res)
    }

    // maybe avoid l:bool by using the swapping option for mh?
    fn can_match_fst_snd_pair(
        &self,
        tm: Tm,
        mh: &MatchHelper,
        l: bool, // tm is the left term
    ) -> BoxRes<bool> {
        // returns true if tm can be matched to components

        Ok(match self.match_fst_snd_pair(tm, mh, l, true)? {
            None => false,
            Some(_) => match self.match_fst_snd_pair(tm, mh, l, false)? {
                Some(_) => true,
                None => {
                    return Err(MyError::new(ErrCode::Impossible));
                }
            },
        })
    }

    fn match_fst_pair(&self, tm: Tm, mh: &MatchHelper, l: bool) -> BoxRes<Tm> {
        //     self.match_fst_snd_pair(tm,mh,l,true)
        myerr::opt2imposs(self.match_fst_snd_pair(tm, mh, l, true)?)
    }

    fn match_snd_pair(&self, tm: Tm, mh: &MatchHelper, l: bool) -> BoxRes<Tm> {
        myerr::opt2imposs(self.match_fst_snd_pair(tm, mh, l, false)?)
    }

    fn match_fst_snd_pair(
        &self,
        tm: Tm,
        mh: &MatchHelper,
        l: bool,
        fst: bool,
    ) -> BoxRes<Option<Tm>> {
        // tries to match with a pair, and returns first component
        //   or returns second component, if !fst

        let (te, _): &(TermEntry, Ty) = self.get_term_entry(tm)?;
        match te {
            Var => {
                if mh.has_def(tm, l) {
                    let new_tm = mh.get_local_def(tm, l)?;
                    self.match_fst_snd_pair(new_tm, mh, l, fst)
                } else {
                    Ok(None)
                }
            }
            Def(new_tm) => self.match_fst_snd_pair(*new_tm, mh, l, fst),
            Pair(tm1, tm2) => Ok(Some(if fst { *tm1 } else { *tm2 })),
            Fst(x) => match self.match_fst_snd_pair(*x, mh, l, true)? {
                None => Ok(None),
                Some(y) => self.match_fst_snd_pair(y, mh, l, fst),
            },
            Snd(x) => match self.match_fst_snd_pair(*x, mh, l, false)? {
                None => Ok(None),
                Some(y) => self.match_fst_snd_pair(y, mh, l, fst),
            },
            ForAll(_) | Lambda(_, _) | FunAp(_, _) | Theorem(_) => {
                Err(MyError::new(ErrCode::Impossible))
            }
        }
    }

    fn match_fst_snd_with_stack(
        &self,
        tm: Tm,
        tm2: Tm,
        mh: &mut MatchHelper,
        l: bool,
    ) -> BoxRes<bool> {
        // tries to match `tm` with `?? tm2`, where
        //  ?? refers to a a fst-snd-combination from the mh stack

        if mh.fst_snd_stack_is_empty() {
            return if l {
                self.match_internal(tm, tm2, mh)
            } else {
                self.match_internal(tm2, tm, mh)
            };
        }

        let (te, _): &(TermEntry, Ty) = self.get_term_entry(tm)?;
        match te {
            Def(new_tm) => self.match_fst_snd_with_stack(*new_tm, tm2, mh, l),
            Var => {
                if mh.has_def(tm, l) {
                    let new_tm = mh.get_local_def(tm, l)?;
                    self.match_fst_snd_with_stack(new_tm, tm2, mh, l)
                } else {
                    Ok(false)
                }
            }
            Fst(x) => match self.match_fst_snd_pair(*x, mh, l, true)? {
                Some(y) => self.match_fst_snd_with_stack(y, tm2, mh, l),
                None => {
                    // reduce stack by one entry
                    let stack_entry = mh.pop_stack()?;
                    if stack_entry {
                        let res = self.match_fst_snd_with_stack(*x, tm2, mh, l);
                        mh.add_to_stack(stack_entry);
                        res
                    } else {
                        mh.add_to_stack(stack_entry);
                        Ok(false)
                    }
                }
            },
            Snd(x) => match self.match_fst_snd_pair(*x, mh, l, false)? {
                Some(y) => self.match_fst_snd_with_stack(y, tm2, mh, l),
                None => {
                    // reduce stack by one entry
                    let stack_entry = mh.pop_stack()?;
                    if stack_entry {
                        // is true if fst
                        mh.add_to_stack(stack_entry);
                        Ok(false)
                    } else {
                        let res = self.match_fst_snd_with_stack(*x, tm2, mh, l);
                        mh.add_to_stack(stack_entry);
                        res
                    }
                }
            },
            Pair(x1, x2) => self.match_pair_unres(*x1, *x2, tm2, mh, l),
            Lambda(_, _) | ForAll(_) | FunAp(_, _) => Ok(false),
            Theorem(_) => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    fn match_pair_unres(
        &self,
        p1: Tm,
        p2: Tm,
        tm2: Tm,
        mh: &mut MatchHelper,
        l: bool,
        //     confirm_empty_stack: bool,
    ) -> BoxRes<bool> {
        // checks if `pr p1 p2` matches `tm2`
        // tm2 cannot be resolved and should be Var,Fst,Snd

        let len = mh.fst_snd_stack.len();

        mh.add_to_stack(true); // load `fst`
        let b = self.match_fst_snd_with_stack(p1, tm2, mh, l)?;
        mh.pop_stack()?;

        mh.confirm_stack_size(len)?;
        if b {
            mh.add_to_stack(false);
            let res = self.match_fst_snd_with_stack(p2, tm2, mh, l)?;
            mh.pop_stack()?;
            mh.confirm_stack_size(len)?;
            Ok(res)
        } else {
            Ok(false)
        }
    }

    fn match_lambda(&self, tm: Tm, mh: &MatchHelper, l: bool) -> BoxRes<Option<Tm>> {
        let (te, _): &(TermEntry, Ty) = self.get_term_entry(tm)?;
        match te {
            Lambda(_, _) => Ok(Some(tm)),
            Var => {
                if mh.has_def(tm, l) {
                    let new_tm = mh.get_local_def(tm, l)?;
                    self.match_lambda(new_tm, mh, l)
                } else {
                    Ok(None)
                }
            }
            Def(new_tm) => self.match_lambda(*new_tm, mh, l),
            Fst(x) if self.can_match_fst_snd_pair(*x, mh, l)? => {
                let new_tm = self.match_fst_pair(*x, mh, l)?;
                self.match_lambda(new_tm, mh, l)
            }
            Snd(x) if self.can_match_fst_snd_pair(*x, mh, l)? => {
                let new_tm = self.match_snd_pair(*x, mh, l)?;
                self.match_lambda(new_tm, mh, l)
            }
            ForAll(_) | Fst(_) | Snd(_) => Ok(None),
            Pair(_, _) | FunAp(_, _) | Theorem(_) => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    fn match_funap_lambda(
        &self,
        fun1: Tm,
        inp1: Tm,
        tm2: Tm,
        mh: &mut MatchHelper,
        l: bool, // (fun1,inp1) are the left term, tm2 is right term
    ) -> BoxRes<Option<bool>> {
        // tries to match `. fun1 inp1` with `tm2`
        // only interested when fun1 is a lambda

        // returns Some(true) if matching, Some(false) if not matching
        // None if do not know

        match self.match_lambda(fun1, mh, l)? {
            None => Ok(None),
            Some(la) => {
                let (var, o) = myerr::opt2imposs(self.destruct_lambda(la))?;

                // add local definition to MatchHelper,
                //   defines variable as input
                let res: bool = mh.add_def(var, inp1, l)?;
                if !res {
                    // problems, we do not want to continue
                    return Ok(None); // None is acceptable here,
                                     // because matching can continue elsewhere
                }

                // try to match output of lambda
                let res: bool = if l {
                    self.match_internal(o, tm2, mh)?
                } else {
                    self.match_internal(tm2, o, mh)?
                };
                mh.remove_def(var, inp1, l)?;
                Ok(Some(res))
            }
        }
    }

    fn match_internal(&self, tm1: Tm, tm2: Tm, mh: &mut MatchHelper) -> BoxRes<bool> {
        // matches two terms, can call itself recursively
        // MatchHelper mh has local definitions and translations
        //  - local defs: when reducing a lambda, define local var
        //      as the input term
        //  - translations: when both match a lambda,
        //      local vars are translated

        // assumes that they have the same type
        if tm1 == tm2 {
            if mh.has_no_terms() {
                return Ok(true);
            }

            // defs (non-local) cannot be disturbed by different local vars
            if self.is_def(tm1)? {
                return Ok(true);
            }
        }
        let (x1, _) = self.get_term_entry(tm1)?;
        let (x2, _) = self.get_term_entry(tm2)?;

        // should we confirm types here? No, for now

        match (x1, x2) {
            // diagonal entries first
            (Var, Var) if mh.is_trans(tm1, tm2)? => Ok(true),
            // also works if tm1 == tm2 and no translations
            //     or local defs registered
            (ForAll(tf1), ForAll(tf2)) => self.match_types(*tf1, *tf2),
            (Lambda(v1, o1), Lambda(v2, o2)) => {
                let res = mh.add_translation(*v1, *v2)?;
                if !res {
                    return Ok(false);
                }
                let res = self.match_internal(*o1, *o2, mh);
                mh.remove_translation(*v1, *v2)?;
                res
            }
            (Pair(y1, z1), Pair(y2, z2)) => {
                let b: bool = self.match_internal(*y1, *y2, mh)?;
                let b = b && self.match_internal(*z1, *z2, mh)?;
                Ok(b)
            }
            (FunAp(f1, i1), FunAp(f2, i2)) => {
                let i1_ty = self.get_type(*i1)?;
                let i2_ty = self.get_type(*i2)?;

                // check if inputs match
                let b: bool = self.match_types(i1_ty, i2_ty)?;
                let b = b && self.match_internal(*i1, *i2, mh)?;
                if b && self.match_internal(*f1, *f2, mh)? {
                    // inputs and functions match
                    Ok(true)
                } else {
                    // inputs or functions do not match
                    match self.match_funap_lambda(*f1, *i1, tm2, mh, true)? {
                        Some(b) => Ok(b),
                        // f1 not matcheable as lambda
                        None => {
                            match self.match_funap_lambda(*f2, *i2, tm1, mh, false)? {
                                Some(b) => Ok(b),
                                // f1 and f2 not matcheable as lambda
                                None => Ok(false),
                            }
                        }
                    }
                }
            }
            // diag entries for Fst,Snd later

            // Deal with Def entries
            (Def(tm), _) => self.match_internal(*tm, tm2, mh),
            (_, Def(tm)) => self.match_internal(tm1, *tm, mh),

            // Deal with many Var entries
            (Var, _) if mh.has_def(tm1, true) => {
                let new_tm1 = mh.get_local_def(tm1, true)?;
                self.match_internal(new_tm1, tm2, mh)
            }
            (_, Var) if mh.has_def(tm2, false) => {
                let new_tm2 = mh.get_local_def(tm2, false)?;
                self.match_internal(tm1, new_tm2, mh)
            }
            // (Var,Var) false, unless equal or local defs or translation
            (Var, Var) => Ok(false),

            // should be false: if true,  should have a def or local def
            (Var, ForAll(_)) => Ok(false),
            (ForAll(_), Var) => Ok(false),

            // consider most Fst/Snd cases
            (Fst(x), _) if self.can_match_fst_snd_pair(*x, mh, true)? => {
                let new_tm = self.match_fst_pair(*x, mh, true)?;
                self.match_internal(new_tm, tm2, mh)
            }
            (_, Fst(x)) if self.can_match_fst_snd_pair(*x, mh, false)? => {
                let new_tm = self.match_fst_pair(*x, mh, false)?;
                self.match_internal(tm1, new_tm, mh)
            }
            (Fst(y1), Fst(y2)) => self.match_internal(*y1, *y2, mh),
            (Snd(x), _) if self.can_match_fst_snd_pair(*x, mh, true)? => {
                let new_tm = self.match_snd_pair(*x, mh, true)?;
                self.match_internal(new_tm, tm2, mh)
            }
            (_, Snd(x)) if self.can_match_fst_snd_pair(*x, mh, false)? => {
                let new_tm = self.match_snd_pair(*x, mh, false)?;
                self.match_internal(tm1, new_tm, mh)
            }
            (Snd(y1), Snd(y2)) => self.match_internal(*y1, *y2, mh),

            // should be false, because otherwise deconstructable
            (Fst(_), ForAll(_)) | (Snd(_), ForAll(_)) => Ok(false),
            (ForAll(_), Fst(_)) | (ForAll(_), Snd(_)) => Ok(false),
            (Fst(_), Snd(_)) | (Snd(_), Fst(_)) => Ok(false),
            (Fst(_), Var) | (Snd(_), Var) => Ok(false),
            (Var, Fst(_)) | (Var, Snd(_)) => Ok(false),

            // Theorems are impossible here anyways
            (Theorem(_), _) => Err(MyError::new(ErrCode::Impossible)),
            (_, Theorem(_)) => Err(MyError::new(ErrCode::Impossible)),

            // cases where types cannot agree:
            (ForAll(_), FunAp(_, _)) => Err(MyError::new(ErrCode::Impossible)),
            (ForAll(_), Pair(_, _)) => Err(MyError::new(ErrCode::Impossible)),
            (FunAp(_, _), ForAll(_)) => Err(MyError::new(ErrCode::Impossible)),
            (Pair(_, _), ForAll(_)) => Err(MyError::new(ErrCode::Impossible)),
            (FunAp(_, _), Pair(_, _)) | (Lambda(_, _), Pair(_, _)) => {
                Err(MyError::new(ErrCode::Impossible))
            }
            (Pair(_, _), FunAp(_, _)) | (Pair(_, _), Lambda(_, _)) => {
                Err(MyError::new(ErrCode::Impossible))
            }
            (FunAp(_, _), Lambda(_, _)) => Err(MyError::new(ErrCode::Impossible)),
            (Lambda(_, _), FunAp(_, _)) => Err(MyError::new(ErrCode::Impossible)),

            (FunAp(f1, i1), _) => match self.match_funap_lambda(*f1, *i1, tm2, mh, true)? {
                Some(b) => Ok(b),
                None => Ok(false),
            },
            (_, FunAp(f2, i2)) => match self.match_funap_lambda(*f2, *i2, tm1, mh, false)? {
                Some(b) => Ok(b),
                None => Ok(false),
            },

            (Pair(y1, y2), _) => {
                // for unresolvable tm2: tm2 should be Var,Fst,Snd
                // others should already be happened or impossible
                mh.confirm_stack_size(0)?;
                self.match_pair_unres(*y1, *y2, tm2, mh, true)
            }
            (_, Pair(y1, y2)) => {
                // for unresolvable tm1: tm1 should be Var,Fst,Snd
                mh.confirm_stack_size(0)?;
                self.match_pair_unres(*y1, *y2, tm1, mh, false)
            }

            // despite some possible edge case for a match here,
            // we say that it is false
            (ForAll(_), Lambda(_, _)) => Ok(false),
            (Lambda(_, _), ForAll(_)) => Ok(false),
            (Lambda(_, _), Var) => Ok(false),
            (Var, Lambda(_, _)) => Ok(false),
            (Fst(_), Lambda(_, _)) | (Snd(_), Lambda(_, _)) => Ok(false),
            (Lambda(_, _), Fst(_)) | (Lambda(_, _), Snd(_)) => Ok(false),
            // maybe add matching for this case?
            // no, because can only appear inside a funap
        }
    }

    pub fn confirm_all_types(&self) -> BoxRes<()> {
        for (tme, ty) in &self.tms {
            match tme {
                Theorem(tm) => {
                    if !(self.is_bool(*tm)? && self.is_theorem_type(*ty)) {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                ForAll(ty2) => {
                    // ty should be `pred pred ty2`
                    let ty3 = self.destruct_pred_type(*ty)?;
                    let ty4 = self.destruct_pred_type(ty3)?;
                    if !self.match_types(ty4, *ty2)? {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                Lambda(var, out) => {
                    // out:`bool`, var:`x`, ty==`pred x`
                    if !self.is_var(*var)? {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                    let ty2 = self.destruct_pred_type(*ty)?;
                    let ty3 = self.get_type(*var)?;
                    if !(self.match_types(ty2, ty3)? && self.is_bool(*out)?) {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                FunAp(fun, inp) => {
                    // ty==`bool`, fun:`pred x`, inp:`x`
                    let inp_ty = self.get_type(*inp)?;
                    let fun_ty = self.get_type(*fun)?;
                    let ty2 = self.destruct_pred_type(fun_ty)?;
                    let ok: bool = self.match_types(inp_ty, ty2)?;
                    if !(ok && self.match_types(*ty, self.bool_type())?) {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                Pair(tm1, tm2) => {
                    // tm1:ty1, tm2:ty2, ty==Pairs(ty1,ty2)
                    let ty1: Ty = self.get_type(*tm1)?;
                    let ty2: Ty = self.get_type(*tm2)?;
                    let (ty3, ty4) = self.destruct_pair_type(*ty)?;
                    let ok: bool = self.match_types(ty1, ty3)?;
                    if !(ok && self.match_types(ty2, ty4)?) {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                Fst(tm) => {
                    // tm:typ
                    let p_ty: Ty = self.get_type(*tm)?;
                    let (ty1, _) = self.destruct_pair_type(p_ty)?;
                    if !self.match_types(ty1, *ty)? {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                Snd(tm) => {
                    // tm:typ
                    let p_ty: Ty = self.get_type(*tm)?;
                    let (_, ty2) = self.destruct_pair_type(p_ty)?;
                    if !self.match_types(ty2, *ty)? {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
                Var => {}
                Def(tm) => {
                    let ty2: Ty = self.get_type(*tm)?;
                    if !self.match_types(ty2, *ty)? {
                        return Err(MyError::new(ErrCode::Impossible));
                    }
                }
            }
        }
        Ok(())
    }
}

#[test]
fn test_type_matching() {
    let mut t = Terms::new();
    let ty1 = t.bool_type();
    let ty2 = t.set_type();
    let ty3: Ty = t.new_pair_type(ty1, ty2);
    let ty4: Ty = t.new_pair_type(ty1, ty2);
    assert!(t.match_types(ty3, ty4).unwrap())
}
