use super::constants;
use super::myerr;
use super::names;
use super::terms;
use super::BoxRes;
use super::ErrCode;
use super::MyError;
use std::collections::HashMap;
use std::collections::HashSet;
use terms::TermEntry;
use terms::Thm;
use terms::Tm;
use terms::TmOrThm;
use terms::Ty;
use terms::TypeEntry;

pub struct Context {
    pub names: names::Names,
    pub terms: terms::Terms,
}

struct PrintHelper {
    local_vars: HashSet<String>,
    alt_names: HashMap<Tm, String>,
}

impl PrintHelper {
    pub fn new() -> PrintHelper {
        PrintHelper {
            local_vars: HashSet::new(),
            alt_names: HashMap::new(),
        }
    }

    fn confirm_clean(&self) -> BoxRes<()> {
        if self.local_vars.is_empty() && self.alt_names.is_empty() {
            Ok(())
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    fn alternative_var_name(&self, v: &str, i: u32) -> String {
        let mut vnew = v.to_string();
        match i {
            0 => {
                vnew.push_str("");
            }
            1 => {
                vnew.push_str("'");
            }
            2 => {
                vnew.push_str("\"");
            }
            j @ 3..=12 => {
                vnew.push_str(&(j - 3).to_string());
            }
            j @ 13..=0xffffffff => {
                let append = format!("_x{:x}", j - 13);
                vnew.push_str(&append);
            }
        }
        vnew
    }

    fn find_unused_alt(&self, v: &str, n: &names::Names) -> BoxRes<String> {
        for i in 0u32..0xffffffffu32 {
            // max u32
            let alt = self.alternative_var_name(v, i);
            if self.local_vars.contains(&alt) || n.has_word(&alt) {
                continue;
            } else {
                return Ok(alt);
            }
        }
        Err(MyError::new(ErrCode::Impossible))
    }

    fn register_local_var(&mut self, n: &names::Names, tm: Tm) -> BoxRes<()> {
        let w = n.get_old_word(tm)?;
        if !n.is_old_term(tm) {
            return Err(MyError::new(ErrCode::Impossible));
        }
        let alt_w = self.find_unused_alt(&w, n)?;
        myerr::expected(true, self.local_vars.insert(alt_w.to_string()))?;
        myerr::some2imposs(self.alt_names.insert(tm, alt_w))
    }

    fn unregister_local_var(&mut self, tm: Tm) -> BoxRes<()> {
        let alt_w = myerr::opt2imposs(self.alt_names.remove(&tm))?;
        myerr::expected(true, self.local_vars.remove(&alt_w))
    }

    fn get_name(&self, tm: Tm) -> BoxRes<String> {
        Ok(myerr::opt2imposs(self.alt_names.get(&tm))?.to_string())
    }
}

impl Context {
    pub fn new() -> BoxRes<Context> {
        let mut c = Context {
            names: names::Names::new(),
            terms: terms::Terms::new(),
        };
        myerr::boxres2imposs(c.init_imp())?;
        Ok(c)
    }

    fn init_imp(&mut self) -> BoxRes<()> {
        // imp should already exist
        let imp: Tm = self.terms.imp_term();
        self.names.add_term_entry(constants::IMP, imp)?;
        Ok(())
    }

    pub fn print_term(&self, tm: Tm) -> BoxRes<String> {
        let mut ph = PrintHelper::new();
        let res = self.print_internal(tm, &mut ph)?;
        ph.confirm_clean()?;
        Ok(res)
    }

    fn print_internal(&self, tm: Tm, ph: &mut PrintHelper) -> BoxRes<String> {
        // can a Tm collide with itself (same number)? -> no
        // note: collisions can only come from new local vars (in \ )

        if self.names.is_old_term(tm) {
            ph.get_name(tm)
        } else if self.names.is_non_old_term(tm) {
            self.names.get_non_old_word(tm)
        } else {
            let (tm_entry, _) = self.terms.get_term_entry(tm)?;
            match tm_entry {
                TermEntry::ForAll(fa_ty) => {
                    let ty_str = self.print_type(*fa_ty)?;
                    Ok(format!("{} {}", constants::FORALL, ty_str))
                }
                TermEntry::Lambda(var, out) => {
                    // note: var has to be an old variable here
                    ph.register_local_var(&self.names, *var)?;
                    let v_s = self.print_internal(*var, ph)?;
                    let o_s = self.print_internal(*out, ph)?;
                    ph.unregister_local_var(*var)?;
                    let v_ty = self.terms.get_type(*var)?;
                    let vts = self.print_type(v_ty)?;
                    Ok(format!("{} {} {} {}", constants::LAMBDA, v_s, vts, o_s))
                }
                TermEntry::FunAp(fun, inp) => {
                    let f_s = self.print_internal(*fun, ph)?;
                    let i_s = self.print_internal(*inp, ph)?;
                    Ok(format!("{} {} {}", constants::FUNAP, f_s, i_s))
                }
                TermEntry::Pair(tm1, tm2) => {
                    let s1 = self.print_internal(*tm1, ph)?;
                    let s2 = self.print_internal(*tm2, ph)?;
                    Ok(format!("{} {} {}", constants::PAIR, s1, s2))
                }
                TermEntry::Fst(tm1) => {
                    let s1 = self.print_internal(*tm1, ph)?;
                    Ok(format!("{} {}", constants::FST, s1))
                }
                TermEntry::Snd(tm2) => {
                    let s2 = self.print_internal(*tm2, ph)?;
                    Ok(format!("{} {}", constants::SND, s2))
                }
                TermEntry::Theorem(_) => Err(MyError::new(ErrCode::Impossible)),
                TermEntry::Var | TermEntry::Def(_) => {
                    // should have found the words in names above
                    Err(MyError::new(ErrCode::Impossible))
                }
            }
        }
    }

    pub fn print_type(&self, ty: Ty) -> BoxRes<String> {
        //     let entry : TypeEntry = myerr::opt2imposs(self.terms.tys.get(ty))?;
        let entry: &TypeEntry = self.terms.get_type_entry(ty)?;
        match entry {
            TypeEntry::Bool => Ok(constants::BOOL.to_string()),
            TypeEntry::Set => Ok(constants::SET.to_string()),
            TypeEntry::Pairs(ty1, ty2) => {
                let s1 = self.print_type(*ty1)?;
                let s2 = self.print_type(*ty2)?;
                Ok(format!("{} {} {}", constants::PAIRS, s1, s2))
            }
            TypeEntry::Pred(ty2) => {
                let s2 = self.print_type(*ty2)?;
                Ok(format!("{} {}", constants::PRED, s2))
            }
            TypeEntry::TheoremType => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    pub fn print_theorem(&self, thm: Thm) -> BoxRes<String> {
        // prints the underlying term with $thm in front
        let thm_tm: Tm = self.terms.thm2bool(thm)?;
        let s: String = self.print_term(thm_tm)?;
        //     Ok(s)
        Ok(format!("{} {}", constants::THM, s))
    }

    pub fn print_bool_type(&self) -> BoxRes<String> {
        self.print_type(self.terms.bool_type())
    }

    pub fn print_word(&self, w: &str) -> BoxRes<String> {
        // prints named vars, thms, or defs
        // make a difference between term and theorem
        // do not print keywords, tell "not allowed" instead

        let mut s = format!("{}: ", constants::PRINT);
        if !self.names.has_word(w) {
            return Err(MyError::new(ErrCode::Impossible));
        }
        if self.names.is_keyword(w) {
            s.push_str(&format!("`{}` is not allowed to print", w));
            return Ok(s);
        }
        // theorem, def or variable
        let tmorthm: TmOrThm = *myerr::opt2imposs(self.names.get_from_word(w))?;
        let is_thm: bool = self.terms.is_thm(tmorthm)?;
        if is_thm {
            let thm_str = self.print_theorem(*tmorthm.get_thm()?)?;
            s.push_str(&format!("Theorem {}: `{}`", w, thm_str));
            return Ok(s);
        }
        let tm: Tm = *tmorthm.get_tm()?;
        let is_def: bool = (!is_thm) && self.terms.is_def(tm)?;
        let is_var: bool = (!is_thm) && self.terms.is_var(tm)?;
        if is_var || is_def {
            let ty = self.terms.get_type(tm)?;
            let ty_str = self.print_type(ty)?;
            s.push_str(&format!("`{}` has type `{}`", w, ty_str));
        }
        if is_def {
            let def_tm: Tm = self.terms.destruct_def(tm)?;
            let def_tm_str = self.print_term(def_tm)?;
            s.push_str(&format!(" and is defined as `{}`", def_tm_str));
        }
        if is_var || is_def || is_thm {
            Ok(s)
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }
}
