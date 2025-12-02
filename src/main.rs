mod ast;
mod infer;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub parser);
use crate::ast::*;
use crate::infer::*;
fn main() {
    use std::io::{self, Write};
    let parser = parser::ExprParser::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let input = input.trim();

        if input.is_empty() {
            continue;
        }

        match parser.parse(input) {
            Ok(expr) => {
                let mut infer = TypeInfer::new();
                match infer.infer(&TypeEnv::new(), &expr) {
                    Ok((_, ty)) => println!("{}", ty),
                    Err(e) => println!("error: {}\n", e),
                }
            }
            Err(e) => println!("error: {}\n", e),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    fn parse_and_infer(input: &str) -> Result<Type, String> {
        let parser = parser::ExprParser::new();
        let expr = parser
            .parse(input)
            .map_err(|e| format!("Parse error: {:?}", e))?;
        let mut infer = TypeInfer::new();
        infer
            .infer(&TypeEnv::new(), &expr)
            .map(|(_, ty)| ty)
            .map_err(|e| e.to_string())
    }

    // 基础类型测试
    #[test]
    fn test_basic_nat() {
        assert_eq!(parse_and_infer("42").unwrap(), Type::TyNat);
    }

    #[test]
    fn test_basic_bool() {
        assert_eq!(parse_and_infer("true").unwrap(), Type::TyBool);
    }

    // IsZero 和 Succ 测试
    #[test]
    fn test_zero_check() {
        assert_eq!(parse_and_infer("zero? 1").unwrap(), Type::TyBool);
    }

    #[test]
    fn test_succ() {
        assert_eq!(parse_and_infer("succ 5").unwrap(), Type::TyNat);
    }

    #[test]
    fn test_zero_check_error() {
        assert!(parse_and_infer("zero? true").is_err());
    }

    // Pair 测试
    #[test]
    fn test_pair() {
        let result = parse_and_infer("(1, true)").unwrap();
        assert_eq!(
            result,
            Type::TyPair(Box::new(Type::TyNat), Box::new(Type::TyBool))
        );
    }

    #[test]
    fn test_fst() {
        assert_eq!(parse_and_infer("fst (1, true)").unwrap(), Type::TyNat);
    }

    #[test]
    fn test_snd() {
        assert_eq!(parse_and_infer("snd (1, true)").unwrap(), Type::TyBool);
    }

    // If 表达式测试
    #[test]
    fn test_if_basic() {
        assert_eq!(
            parse_and_infer("if true then 1 else 2").unwrap(),
            Type::TyNat
        );
    }

    #[test]
    fn test_if_bool_result() {
        assert_eq!(
            parse_and_infer("if zero? 0 then true else false").unwrap(),
            Type::TyBool
        );
    }

    #[test]
    fn test_if_type_mismatch() {
        assert!(parse_and_infer("if true then 1 else false").is_err());
    }

    #[test]
    fn test_if_condition_not_bool() {
        assert!(parse_and_infer("if 1 then 2 else 3").is_err());
    }

    // Lambda 和 App 测试
    #[test]
    fn test_identity() {
        let result = parse_and_infer("\\x => x").unwrap();
        match result {
            Type::TyArrow(_, _) => (),
            _ => panic!("Expected arrow type"),
        }
    }

    #[test]
    fn test_app_simple() {
        assert_eq!(parse_and_infer("(\\x => x) 5").unwrap(), Type::TyNat);
    }

    #[test]
    fn test_const_function() {
        assert_eq!(parse_and_infer("(\\x => 42) true").unwrap(), Type::TyNat);
    }

    // Let 多态测试
    #[test]
    fn test_polymorphic_let() {
        let result = parse_and_infer("let f = \\x => x in (f 1, f true)").unwrap();
        assert_eq!(
            result,
            Type::TyPair(Box::new(Type::TyNat), Box::new(Type::TyBool))
        );
    }

    #[test]
    fn test_let_simple() {
        assert_eq!(parse_and_infer("let x = 5 in x").unwrap(), Type::TyNat);
    }

    #[test]
    fn test_let_used_twice() {
        assert_eq!(parse_and_infer("let x = 5 in succ x").unwrap(), Type::TyNat);
    }

    // Lambda 不是多态的（与 let 对比）
    #[test]
    fn test_lambda_not_polymorphic() {
        // 这应该失败，因为 lambda 参数不是多态的
        assert!(parse_and_infer("(\\f => (f 1, f true)) (\\x => x)").is_err());
    }

    // 嵌套 Let
    #[test]
    fn test_nested_let() {
        assert_eq!(
            parse_and_infer("let x = 5 in let y = 10 in x").unwrap(),
            Type::TyNat
        );
    }

    #[test]
    fn test_let_shadowing() {
        assert_eq!(
            parse_and_infer("let x = 5 in let x = true in x").unwrap(),
            Type::TyBool
        );
    }

    // 复杂组合测试
    #[test]
    fn test_complex_pair_fst() {
        assert_eq!(
            parse_and_infer("let p = (1, true) in fst p").unwrap(),
            Type::TyNat
        );
    }

    #[test]
    fn test_function_in_pair() {
        let result = parse_and_infer("let f = \\x => x in (f, f)").unwrap();
        match result {
            Type::TyPair(_, _) => (),
            _ => panic!("Expected pair type"),
        }
    }

    #[test]
    fn test_higher_order() {
        // (\\f => f 5) (\\x => x)
        assert_eq!(
            parse_and_infer("(\\f => f 5) (\\x => x)").unwrap(),
            Type::TyNat
        );
    }

    #[test]
    fn test_compose_like() {
        // let f = \x => succ x in let g = \y => zero? y in g (f 0)
        assert_eq!(
            parse_and_infer("let f = \\x => succ x in let g = \\y => zero? y in g (f 0)").unwrap(),
            Type::TyBool
        );
    }

    // 复杂的多态测试
    #[test]
    fn test_polymorphic_twice() {
        // let id = \x => x in let a = id 1 in let b = id true in (a, b)
        let result =
            parse_and_infer("let id = \\x => x in let a = id 1 in let b = id true in (a, b)")
                .unwrap();
        assert_eq!(
            result,
            Type::TyPair(Box::new(Type::TyNat), Box::new(Type::TyBool))
        );
    }

    // If 中的类型推导
    #[test]
    fn test_if_with_inference() {
        // if zero? 0 then (\x => x) else (\y => y)
        let result = parse_and_infer("if zero? 0 then (\\x => x) else (\\y => y)").unwrap();
        match result {
            Type::TyArrow(_, _) => (),
            _ => panic!("Expected arrow type"),
        }
    }

    // Pair 嵌套
    #[test]
    fn test_nested_pairs() {
        let result = parse_and_infer("((1, 2), (true, false))").unwrap();
        assert_eq!(
            result,
            Type::TyPair(
                Box::new(Type::TyPair(Box::new(Type::TyNat), Box::new(Type::TyNat))),
                Box::new(Type::TyPair(Box::new(Type::TyBool), Box::new(Type::TyBool)))
            )
        );
    }

    // 错误情况测试
    #[test]
    fn test_unbound_variable() {
        assert!(parse_and_infer("x").is_err());
    }

    #[test]
    fn test_app_non_function() {
        assert!(parse_and_infer("5 10").is_err());
    }

    #[test]
    fn test_fst_non_pair() {
        assert!(parse_and_infer("fst 5").is_err());
    }

    // 递归类型检测（infinite type）
    #[test]
    fn test_self_application() {
        // \x => x x 应该产生 infinite type 错误
        assert!(parse_and_infer("\\x => x x").is_err());
    }

    // 复杂的高阶函数
    #[test]
    fn test_apply_twice() {
        // let twice = \f => \x => f (f x) in twice (\y => succ y) 0
        assert_eq!(
            parse_and_infer("let twice = \\f => \\x => f (f x) in twice (\\y => succ y) 0")
                .unwrap(),
            Type::TyNat
        );
    }

    #[test]
    fn test_const_combinator() {
        // let const = \x => \y => x in const 5 true
        assert_eq!(
            parse_and_infer("let const = \\x => \\y => x in const 5 true").unwrap(),
            Type::TyNat
        );
    }

    // Let 中使用函数
    #[test]
    fn test_let_with_function_body() {
        assert_eq!(
            parse_and_infer("let f = \\x => succ x in f 0").unwrap(),
            Type::TyNat
        );
    }

    // 类型推导传播
    #[test]
    fn test_type_propagation() {
        // let f = \x => if zero? x then 0 else x in f 5
        assert_eq!(
            parse_and_infer("let f = \\x => if zero? x then 0 else x in f 5").unwrap(),
            Type::TyNat
        );
    }

    // 测试嵌套的if表达式
    #[test]
    fn test_nested_if() {
        let result = parse_and_infer("if zero? 0 then if true then 1 else 2 else 3").unwrap();
        assert_eq!(result, Type::TyNat);
    }
    // 测试if zero? 0 then (\x => x) else (\y => succ y)
    #[test]
    fn test_if_with_different_branches() {
        let result = parse_and_infer("if zero? 0 then (\\x => x) else (\\y => succ y)").unwrap();
        assert_eq!(
            result,
            Type::TyArrow(Box::new(Type::TyNat), Box::new(Type::TyNat))
        );
    }
}
