use super::constants;
use super::myerr;
use super::terms::Thm;
use super::terms::Tm;
use super::terms::TmOrThm;
use super::BoxRes;
use super::ErrCode;
use super::MyError;
use std::collections::HashMap;
use std::collections::HashSet;

pub struct Names {
    str2num: HashMap<String, TmOrThm>,
    num2str: HashMap<TmOrThm, String>,
    old_vars: HashMap<Tm, String>,
    keywords: HashSet<String>,
}

impl Names {
    pub fn new() -> Names {
        Names {
            str2num: HashMap::new(),
            num2str: HashMap::new(),
            old_vars: HashMap::new(),
            keywords: HashSet::new(),
        }
    }

    pub fn add_keyword(&mut self, kw: &str) -> BoxRes<()> {
        if self.has_word(kw) {
            Err(MyError::new(ErrCode::Impossible))
        } else {
            self.keywords.insert(kw.to_string());
            Ok(())
        }
    }

    pub fn remove_keyword(&mut self, kw: &str) -> BoxRes<()> {
        // only use when you are sure that thm is present
        match self.keywords.remove(kw) {
            true => Ok(()),
            false => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    pub fn has_word(&self, w: &str) -> bool {
        // returns true if word is known
        self.str2num.contains_key(w) || self.keywords.contains(w)
    }

    pub fn is_keyword(&self, w: &str) -> bool {
        self.keywords.contains(w)
    }

    pub fn add_term_entry(&mut self, w: &str, t: Tm) -> BoxRes<()> {
        self.add_entry(w, TmOrThm::from_tm(t))
    }

    pub fn add_thm_entry(&mut self, w: &str, t: Thm) -> BoxRes<()> {
        self.add_entry(w, TmOrThm::from_thm(t))
    }

    pub fn remove_thm_entry(&mut self, w: &str, t: Thm) -> BoxRes<()> {
        self.remove_entry(w, TmOrThm::from_thm(t))
    }

    pub fn add_entry(&mut self, w: &str, t: TmOrThm) -> BoxRes<()> {
        if self.has_word(w) {
            // should only be used when possible
            Err(MyError::new(ErrCode::Impossible))
        } else {
            //       self.num2str.insert(t, w.to_string());
            //       self.str2num.insert(w.to_string(), t);
            myerr::some2imposs(self.num2str.insert(t, w.to_string()))?;
            myerr::some2imposs(self.str2num.insert(w.to_string(), t))
        }
    }

    pub fn is_old_term(&self, tm: Tm) -> bool {
        self.old_vars.contains_key(&tm)
    }

    pub fn is_non_old_term(&self, tm: Tm) -> bool {
        self.num2str.contains_key(&TmOrThm::from_tm(tm))
    }

    //   pub fn get_word(&self, tm: Tm) -> BoxRes<String> {
    //     let s: &str = match self.num2str.get(&tm) {
    //       None => myerr::opt2imposs(self.old_vars.get(&tm))?,
    //       Some(x) => x,
    //     };
    //     Ok(s.to_string())
    //   }

    pub fn get_non_old_word(&self, tm: Tm) -> BoxRes<String> {
        Ok(myerr::opt2imposs(self.num2str.get(&TmOrThm::from_tm(tm)))?.to_string())
    }

    pub fn get_old_word(&self, tm: Tm) -> BoxRes<String> {
        Ok(myerr::opt2imposs(self.old_vars.get(&tm))?.to_string())
    }

    pub fn remove_entry(&mut self, w: &str, t: TmOrThm) -> BoxRes<()> {
        if self.remove_entry_2(w, t) {
            Ok(())
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    fn remove_entry_2(&mut self, w: &str, t: TmOrThm) -> bool {
        // should return true if everything goes right
        match (self.str2num.remove(w), self.num2str.remove(&t)) {
            (Some(t2), Some(w2)) => t2 == t && w2 == w,
            _ => false,
        }
    }

    pub fn transfer_entry(&mut self, w: &str, tm: Tm) -> BoxRes<()> {
        // transfers entry to old forgotten local variables
        if self.remove_entry_2(w, TmOrThm::from_tm(tm)) {
            match self.old_vars.insert(tm, w.to_string()) {
                None => Ok(()),
                Some(_) => Err(MyError::new(ErrCode::Impossible)),
            }
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    pub fn get_from_word(&self, w: &str) -> Option<&TmOrThm> {
        self.str2num.get(w)
    }

    pub fn add_many_keywords(&mut self) -> BoxRes<()> {
        self.add_keyword(constants::FUNAP)?;
        self.add_keyword(constants::LAMBDA)?;
        self.add_keyword(constants::PAIR)?;
        self.add_keyword(constants::FST)?;
        self.add_keyword(constants::SND)?;
        self.add_keyword(constants::PRINT)?;
        self.add_keyword(constants::VAR)?;
        self.add_keyword(constants::ASM)?;
        self.add_keyword(constants::THM)?;
        self.add_keyword(constants::DEF)?;
        self.add_keyword(constants::PROVE)?;
        self.add_keyword(constants::BOOL)?;
        self.add_keyword(constants::SET)?;
        self.add_keyword(constants::PAIRS)?;
        self.add_keyword(constants::PRED)?;
        self.add_keyword(constants::SPEC)?;
        self.add_keyword(constants::MP)?;
        self.add_keyword(constants::FORALL)?;
        // not IMP
        Ok(())
    }
}
