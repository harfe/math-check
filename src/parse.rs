// use super::myerr;
use super::constants;
use super::reader::Reader;
use super::BoxRes;
use super::ErrCode;
use super::MyError;
// use super::names;
// use super::terms;
// use super::types;
use super::context;
// use names::Names;
use super::terms::Thm;
use super::terms::Tm;
use super::terms::TmOrThm;
use super::terms::Ty;
use context::Context;

// type Tm = usize;
// type Thm = Tm; // TODO: change
// type Ty = usize;

// call a function with a location pop()
fn with_lp<F, T>(func: F, r: &mut Reader, c: &mut Context) -> BoxRes<T>
where
    F: Fn(&mut Reader, &mut Context) -> BoxRes<T>,
{
    // call function
    let res = func(r, c)?;
    r.loc_pop()?;
    Ok(res)
}

pub fn parse_file(r: &mut Reader) -> BoxRes<()> {
    let mut context = Context::new()?;
    //   myerr::boxres2imposs(add_many_keywords(&mut context.names))?;
    context.names.add_many_keywords()?;

    // main part
    with_lp(parse_thm, r, &mut context)?;

    context.terms.confirm_all_types()?;

    // confirm that the location stack is empty
    r.confirm_empty_loc_stack()?;

    // confirm that rest of file does not contain any words
    r.confirm_eof()
}

fn parse_thm(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // should return a theorem
    let word = r.word_exp("<thm>")?;
    r.loc_push();
    match &word as &str {
        constants::VAR => parse_var(r, c),
        constants::ASM => parse_asm(r, c),
        constants::DEF => parse_def(r, c),
        constants::PRINT => parse_print(r, c),
        constants::SPEC => parse_spec(r, c),
        constants::PROVE => parse_prove(r, c),
        constants::MP => parse_mp(r, c),
        constants::THM => {
            // parse a named theorem

            // parse the name of the theorem
            let w = parse_new_word(r, c)?;

            // temporarily add as keyword to block the word
            c.names.add_keyword(&w)?;

            // parse the theorem for the name
            let thm1: Thm = with_lp(parse_thm, r, c)?;

            // repackage the theorem. It gets a unique number this way
            let thm_tm: Tm = c.terms.thm2bool(thm1)?;
            let thm1: Thm = c.terms.bool2thm(thm_tm)?;

            // remove temporary keyword, allows word to be used
            c.names.remove_keyword(&w)?;

            // store theorem with name
            c.names.add_thm_entry(&w, thm1)?;

            // continue parsing
            let thm2: Thm = with_lp(parse_thm, r, c)?;

            // remove named theorem
            c.names.remove_thm_entry(&w, thm1)?;

            // return the second theorem
            Ok(thm2)
        }
        w => {
            if let Some(tmthm) = c.names.get_from_word(w) {
                let is_thm: bool = c.terms.is_thm(*tmthm)?;
                if is_thm {
                    return Ok(*TmOrThm::get_thm(tmthm)?);
                }
            }
            let mut e = MyError::new(ErrCode::UnknownThm);
            e.set_got(w);
            e.set_last_location_from_reader(r);
            Err(e)
        }
    }
}

fn parse_term(r: &mut Reader, c: &mut Context) -> BoxRes<Tm> {
    let word = r.word_exp("<term>")?;
    r.loc_push();
    match &word as &str {
        constants::LAMBDA => parse_lambda(r, c),
        constants::FUNAP => parse_funap(r, c),
        constants::PAIR => {
            let fst = with_lp(parse_term, r, c)?;
            let snd = with_lp(parse_term, r, c)?;
            let pair_tm = c.terms.new_pair(fst, snd)?;
            Ok(pair_tm)
        }
        constants::FST => {
            let p = parse_pair(r, c)?;
            let fst_tm = c.terms.new_fst(p)?;
            Ok(fst_tm)
        }
        constants::SND => {
            let p = parse_pair(r, c)?;
            let snd_tm = c.terms.new_snd(p)?;
            Ok(snd_tm)
        }
        constants::FORALL => {
            let ty = parse_type(r, c)?;
            Ok(c.terms.new_forall(ty))
        }
        w => {
            if let Some(tmorthm) = c.names.get_from_word(w) {
                let is_tm: bool = !c.terms.is_thm(*tmorthm)?;
                if is_tm {
                    return Ok(*tmorthm.get_tm()?);
                }
            }
            let mut e = MyError::new(ErrCode::UnknownVar);
            e.set_got(w);
            e.set_last_location_from_reader(r);
            Err(e)
        }
    }
}

fn parse_var(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem
    let w = parse_new_word(r, c)?;
    let ty: Ty = parse_type(r, c)?;

    // create new term for variable
    let tm: Tm = c.terms.new_var(ty);
    c.names.add_term_entry(&w, tm)?;

    // continue parsing
    let thm = with_lp(parse_thm, r, c)?;

    // remove variable
    // c.names.remove_entry(&w,tm)?;

    // transfer variable, old local var
    c.names.transfer_entry(&w, tm)?;

    // returns thm with forall, lambda
    c.terms.var2thm(thm, tm)
}

fn parse_asm(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem
    let w = parse_new_word(r, c)?;

    // use keywords to block w for the next term
    c.names.add_keyword(&w)?;
    let b: Tm = parse_bool(r, c)?;
    c.names.remove_keyword(&w)?;
    let asm: Thm = c.terms.bool2thm(b)?;

    c.names.add_thm_entry(&w, asm)?;

    // continue parsing
    let thm: Thm = with_lp(parse_thm, r, c)?;
    c.names.remove_thm_entry(&w, asm)?;

    // add assumption using imp
    c.terms.asm2thm(thm, asm)
}

fn parse_bool(r: &mut Reader, c: &mut Context) -> BoxRes<Tm> {
    // returns a term
    let b: Tm = parse_term(r, c)?;
    let loc = r.loc_pop()?;
    let is_bool = c.terms.is_bool(b)?;
    if is_bool {
        Ok(b)
    } else {
        let mut e = MyError::new(ErrCode::ExpectedType);
        let bool_str = c.print_bool_type()?;
        e.set_expect(&bool_str);
        e.set_got_term_with_type(b, c);
        e.set_location_pair(loc);
        Err(e)
    }
}

fn parse_mp(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem

    // parse the first theorem, should be an imp statement
    let thm1 = parse_thm(r, c)?;
    let loc = r.loc_pop()?;
    let destr_imp = c.terms.destruct_imp_thm(thm1);
    match destr_imp {
        Err(mut e) => {
            e.set_got(&c.print_theorem(thm1)?);
            e.set_location_pair(loc);
            Err(e)
        }
        Ok((p, q)) => {
            // p and q are of type `bool`
            // parse the second theorem
            let thm2 = parse_thm(r, c)?;
            let loc = r.loc_pop()?;
            if c.terms.match_thm_term(thm2, p)? {
                c.terms.bool2thm(q)
            } else {
                let mut e = MyError::new(ErrCode::MpMatch);
                let goal_str = c.print_term(p)?;
                e.set_expect(&goal_str);
                let thm_str = c.print_theorem(thm2)?;
                e.set_got(&thm_str);
                e.set_location_pair(loc);
                Err(e)
            }
        }
    }
}

fn parse_prove(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem

    // statement to be proven
    let goal = parse_bool(r, c)?;

    // theorem as proof
    let thm = parse_thm(r, c)?;
    let loc = r.loc_pop()?;

    if c.terms.match_thm_term(thm, goal)? {
        c.terms.bool2thm(goal)
    } else {
        let mut e = MyError::new(ErrCode::ProveMatch);
        let goal_str = c.print_term(goal)?;
        e.set_expect(&goal_str);
        let thm_str = c.print_theorem(thm)?;
        e.set_got(&thm_str);
        e.set_location_pair(loc);
        Err(e)
    }
}

fn parse_spec(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem

    // parse the general theorem
    let gen: Thm = parse_thm(r, c)?;
    let loc = r.loc_pop()?;
    let destr_fa = c.terms.destruct_forall_thm(gen);
    match destr_fa {
        Err(mut e) => {
            e.set_got(&c.print_theorem(gen)?);
            e.set_location_pair(loc);
            Err(e)
        }
        Ok((fun, fa_ty)) => {
            let tm = parse_term(r, c)?;
            let loc = r.loc_pop()?;
            let tm_ty = c.terms.get_type(tm)?;
            if !c.terms.match_types(tm_ty, fa_ty)? {
                let mut e = MyError::new(ErrCode::ExpectedType);
                let fa_ty_str = c.print_type(fa_ty)?;
                e.set_expect(&fa_ty_str);
                e.set_got_term_with_type(tm, c);
                e.set_location_pair(loc);
                Err(e)
            } else {
                let funap = c.terms.new_funap(fun, tm)?;
                c.terms.bool2thm(funap)
            }
        }
    }
}

fn parse_print(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem
    let w = r.word_exp("<known_word>")?;
    if !c.names.has_word(&w) {
        let mut e = MyError::new(ErrCode::UnknownWord);
        e.set_got(&w);
        e.set_last_location_from_reader(r);
        Err(e)
    } else {
        let text = c.print_word(&w)?;
        println!("{}", text);

        // continue parsing
        let thm = with_lp(parse_thm, r, c)?;
        Ok(thm)
    }
}

fn parse_def(r: &mut Reader, c: &mut Context) -> BoxRes<Thm> {
    // returns a theorem

    let w = parse_new_word(r, c)?;
    // block w for parsing the term
    c.names.add_keyword(&w)?;
    let tm = with_lp(parse_term, r, c)?;
    // let ty:Ty = c.terms.get_type(tm)?;
    c.names.remove_keyword(&w)?;

    // add definition
    let def = c.terms.new_def(tm)?;
    c.names.add_term_entry(&w, def)?;

    // continue parsing
    let thm = with_lp(parse_thm, r, c)?;

    // remove named def again
    // c.names.remove_entry(&w,def)?;

    // transfer variable, old local var
    // def will be converted into a var in def2thm()
    c.names.transfer_entry(&w, def)?;

    // convert into theorem, using funap, lambda
    c.terms.def2thm(thm, def)
}

fn parse_lambda(r: &mut Reader, c: &mut Context) -> BoxRes<Tm> {
    // returns a term

    // parse variable name
    let v = parse_new_word(r, c)?;
    // parse a type for the variable
    let v_ty = parse_type(r, c)?;

    // add new variable
    let v_tm: Tm = c.terms.new_var(v_ty);
    c.names.add_term_entry(&v, v_tm)?;

    // parse the main term
    let tm: Tm = parse_bool(r, c)?;

    // remove variable again
    // c.names.remove_entry(&v,v_tm)?;

    // transfer variable, old local var
    c.names.transfer_entry(&v, v_tm)?;

    c.terms.new_lambda(v_tm, tm)
}

fn parse_funap(r: &mut Reader, c: &mut Context) -> BoxRes<Tm> {
    // returns a term

    let fun = parse_term(r, c)?;
    let loc = r.loc_pop()?;
    let fun_ty: Ty = c.terms.get_type(fun)?;

    if !c.terms.is_pred_type(fun_ty)? {
        let mut e = MyError::new(ErrCode::ExpectedType);
        e.set_expect(&format!("{} {}", constants::PRED, constants::WILDCARD));
        e.set_got_term_with_type(fun, c);
        e.set_location_pair(loc);
        return Err(e);
    }
    let inp = parse_term(r, c)?;
    let loc = r.loc_pop()?;

    // now fun should have type `pred x`
    // and inp should have type `x`
    if c.terms.funap_type_check(fun, inp)? {
        c.terms.new_funap(fun, inp)
    } else {
        let dom_ty: Ty = c.terms.destruct_pred_type(fun_ty)?;
        let mut e = MyError::new(ErrCode::ExpectedType);
        let dom_str = c.print_type(dom_ty)?;
        e.set_expect(&dom_str);
        e.set_got_term_with_type(inp, c);
        e.set_location_pair(loc);
        Err(e)
    }
}

fn parse_pair(r: &mut Reader, c: &mut Context) -> BoxRes<Tm> {
    // returns a term of type `pair x y`

    let p = parse_term(r, c)?;
    let loc = r.loc_pop()?;
    if c.terms.is_pair(p)? {
        Ok(p)
    } else {
        let mut e = MyError::new(ErrCode::ExpectedType);
        e.set_expect(&format!(
            "{} {} {}",
            constants::PAIRS,
            constants::WILDCARD,
            constants::WILDCARD,
        ));
        e.set_got_term_with_type(p, c);
        e.set_location_pair(loc);
        Err(e)
    }
}

fn parse_new_word(r: &mut Reader, c: &mut Context) -> BoxRes<String> {
    let w = r.word_exp("<new_word>")?;
    if c.names.has_word(&w) {
        let mut e = MyError::new(ErrCode::UsedWord);
        e.set_got(&w);
        r.add_last_loc(Err(e))
    } else {
        Ok(w)
    }
}

fn parse_type(r: &mut Reader, c: &mut Context) -> BoxRes<Ty> {
    // returns a type

    let w = r.word_exp("<type>")?;
    match &w as &str {
        constants::SET => Ok(c.terms.set_type()),
        constants::BOOL => Ok(c.terms.bool_type()),
        constants::PAIRS => {
            let fst: Ty = parse_type(r, c)?;
            let snd: Ty = parse_type(r, c)?;
            Ok(c.terms.new_pair_type(fst, snd))
        }
        constants::PRED => {
            let of = parse_type(r, c)?;
            Ok(c.terms.new_pred_type(of))
        }
        x => {
            let mut e = MyError::new(ErrCode::Expected);
            e.set_expect("<type>");
            e.set_got(&format!("\"{}\"", x));
            r.add_last_loc(Err(e))
        }
    }
}

// #[test]

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_err_ascii() {
        let t: String = "µ".to_string();
        let mut r: Reader = Reader::new(&t);
        if let Err(e) = parse_file(&mut r) {
            // assert!(e.has_error(ErrCode::Ascii));
            assert_eq!(e.exit_code(), 6);
        } else {
            assert!(false); // expected error, not Ok
        }
        let t: String = (7u8 as char).to_string();
        let mut r: Reader = Reader::new(&t);
        if let Err(e) = parse_file(&mut r) {
            // assert!(e.has_error(ErrCode::AsciiCtrl));
            assert_eq!(e.exit_code(), 6);
        } else {
            assert!(false); // expected error, not Ok
        }
    }

    fn parse_string_expect_err(t: &str, ec: ErrCode) {
        // only for exit code 1
        let mut r: Reader = Reader::new(&t);
        if let Err(e) = parse_file(&mut r) {
            assert_eq!(e.exit_code(), 1);
            assert!(e.has_error(ec));
        } else {
            assert!(false); // expected error, not Ok
        }
    }

    fn match_testing(t: &str, expected: bool) -> bool {
        let mut r: Reader = Reader::new(&t);
        if let Err(e) = parse_file(&mut r) {
            println!("{}", e.output());
            (!expected) && e.exit_code() == 1 && e.has_error(ErrCode::ProveMatch)
        } else {
            expected
        }
    }

    #[test]
    fn test_match_1() {
        let t = "$var false bool $var true bool $asm ax-true true
      $prove true ax-true";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool $asm ax-true true
      $prove false ax-true";
        assert!(match_testing(t, false));
        let t = "$var false bool $var true bool $asm ax-true true
      $prove . \\ x bool true false ax-true";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool $asm ax-true true
      $def id \\ x bool x
      $thm true2 $prove . id true ax-true
      true2";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool $asm ax-true true
      $def id \\ x bool x
      $thm true2 $prove . id true ax-true
      $prove . id false true2";
        assert!(match_testing(t, false));
        let t = "$var false bool $var true bool # $asm ax-true true
      $def id \\ x bool x
      $asm true2 . id true # ax-true
      $prove . id false true2";
        assert!(match_testing(t, false));
        let t = "$var false bool $var true bool # $asm ax-true true
      $asm true2 . -> : true true # ax-true
      $prove . -> : true true true2";
        assert!(match_testing(t, true));
    }

    #[test]
    fn test_match_2() {
        let t = "$var false bool $var true bool
      $var x pairs pairs bool set bool
      $var y pred pairs bool set
      $asm a1 . y : fst fst x snd fst x
      $prove . y fst x a1";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $def id \\ x bool x
      $asm a1 . \\ x pred bool . ! bool x id
      $prove . ! bool id a1";
        // test forall/lambda match
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $var z set
      $var y pred set
      $asm a1 . y z
      $prove . \\ x set . y x z a1";
        // test var/lambda match
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $def id \\ x bool x
      $asm true2 . id . id true
      $prove . id . id true true2";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $def id \\ x bool x
      $asm true2 . id . id true
      $prove . id . id false true2";
        assert!(match_testing(t, false));
        let t = "$var false bool $var true bool
      $var x pairs pairs bool set bool
      $var y pred pairs pairs bool set bool
      $asm a1 . y : : fst fst x snd fst x snd x
      $prove . y x a1";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $var x pairs pairs bool set bool
      $var y pred pairs pairs bool set bool
      $asm a1 . y : : snd x snd fst x snd x
      $prove . y x a1";
        assert!(match_testing(t, false));
    }

    #[test]
    pub fn test_match_3() {
        let t = "$var false bool $var true bool
      $var z set
      $var g pred pairs set bool
      $def l1 \\ y bool . \\ x set . g : x y z
      $def l2 \\ y bool . \\ x set . g : x y z
      $def d1 \\ zz bool . l1 . l1 zz
      $def d2 \\ zz bool . l2 . l2 true
      $asm a1 . d1 true
      $prove . d2 true a1";
        assert!(match_testing(t, true));
    }

    #[test]
    pub fn test_inputs_1() {
        // should all work
        let t = "$var false bool $var true bool
      $asm axiom-true true
      $thm main axiom-true
      main";
        assert!(match_testing(t, true));
        let t = "$var false bool $var true bool
      $asm axiom-true true
      $def not \\ x bool . -> : x false
      $def exists \\ f pred set
        . not . ! set \\ x set . not . f x
      $print false
      $print exists
      axiom-true";
        assert!(match_testing(t, true));
    }

    #[test]
    fn test_unknown_errors() {
        let t = "$var false bool $var true bool $asm ax-true true
      $prove . \\\\ x bool true false ax-true";
        parse_string_expect_err(t, ErrCode::UnknownVar);
        let t = "$var false bool $var true bool $asm ax-true true
      $prove . \\ x bool true false var";
        parse_string_expect_err(t, ErrCode::UnknownThm);
    }
}
