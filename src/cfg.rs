use yultsur::visitor::ASTVisitor;
use yultsur::yul;

use std::collections::HashMap;

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Node(usize);

#[derive(Clone, Hash, PartialEq, Debug)]
pub enum Edge {
    Empty,
    IfHeader,
    IfTrueBranch(yul::Expression),
    IfFalseBranch(yul::Expression),
    AfterIf,
    SwitchHeader,
    SwitchCase(yul::Expression, Option<yul::Literal>),
    AfterSwitch,
    LoopHeader,
    LoopBody(yul::Expression),
    LoopFalse(yul::Expression),
    LoopPost,
    LoopBack,
    AfterLoop,
    Break,
    Continue,
    Leave,
    FunctionEntry,
    FunctionExit,
}

#[derive(Clone, Debug)]
pub struct CFG {
    pub graph: HashMap<Node, Vec<(Node, Edge)>>,
    pub rev_graph: HashMap<Node, Vec<(Node, Edge)>>,
    pub blocks: HashMap<Node, yul::Block>,
    // (function_entry, function_exit)
    pub functions: HashMap<String, (Node, Node)>,
}

impl CFG {
    pub fn new() -> CFG {
        CFG {
            graph: HashMap::new(),
            rev_graph: HashMap::new(),
            blocks: HashMap::new(),
            functions: HashMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CFGBuilder {
    cfg: CFG,
    counter: usize,
    current: Node,
    statement_acc: Vec<yul::Statement>,
    // TODO replace \/ by a Stack
    // (loop head, after loop), used by `continue` and `break`
    loops: Vec<(Node, Node)>,
    // TODO replace \/ by a Stack
    // function name, used by `leave` to find `function_exit` from `cfg.functions`
    fun_defs: Vec<String>,
}

impl CFGBuilder {
    pub fn new() -> CFGBuilder {
        CFGBuilder {
            cfg: CFG::new(),
            counter: 0,
            current: Node(0),
            statement_acc: vec![],
            loops: vec![],
            fun_defs: vec![],
        }
    }

    pub fn build(ast: yul::Statement) -> CFG {
        let mut builder = CFGBuilder::new();

        builder.add_node(builder.current.clone());
        builder.add_rev_node(builder.current.clone());

        builder.visit_statement(&ast);

        builder.save_acc();

        builder.add_node(builder.current.clone());
        builder.add_rev_node(builder.current.clone());

        builder.cfg.clone()
    }

    fn new_node(&mut self) -> Node {
        self.counter += 1;
        Node(self.counter)
    }

    fn set_current(&mut self, node: Node) {
        self.current = node;
    }

    fn save_acc(&mut self) {
        self.cfg.blocks.insert(
            self.current.clone(),
            yul::Block {
                statements: std::mem::take(&mut self.statement_acc)
            },
        );
        // TODO assert that the insertion happened
    }

    fn add_node(&mut self, from: Node) {
        self.cfg.graph.entry(from).or_insert_with(|| vec![]);
    }

    fn add_rev_node(&mut self, to: Node) {
        self.cfg.rev_graph.entry(to).or_insert_with(|| vec![]);
    }

    fn connect(&mut self, from: Node, to: Node, edge: Edge) {
        self.add_node(from.clone());
        self.add_rev_node(to.clone());

        self.cfg.graph.get_mut(&from).unwrap().push((to.clone(), edge.clone()));
        self.cfg.rev_graph.get_mut(&to).unwrap().push((from, edge));
    }
    fn is_builtin(fun_name: &String) -> bool {
        false
    }

    fn create_function_def_nodes(&mut self, fun_name: &String) {
        let fun_entry = self.new_node();
        let fun_exit = self.new_node();
        self.cfg
            .functions
            .insert(fun_name.clone(), (fun_entry.clone(), fun_exit.clone()));
    }

    fn function_def_nodes(&mut self, fun_name: &String) -> (Node, Node) {
        if !self.cfg.functions.contains_key(fun_name) {
            self.create_function_def_nodes(fun_name);
        }

        self.cfg.functions.get(fun_name).unwrap().clone()
    }

    fn create_function_def_cfg(&mut self, fun: &yul::FunctionDefinition) {
        assert!(self.statement_acc.is_empty());

        self.function_def_nodes(&fun.name.name);

        let (entry, exit) = self
            .cfg
            .functions
            .get_mut(&fun.name.name)
            .unwrap()
            .clone();

        self.set_current(entry);
        self.visit_block(&fun.body);
        self.save_acc();

        self.connect(self.current.clone(), exit, Edge::Empty);
    }

}

impl ASTVisitor for CFGBuilder {
    fn enter_variable_declaration(&mut self, variable: &yul::VariableDeclaration) {
        self.statement_acc.push(yul::Statement::VariableDeclaration(variable.clone()));
    }
    fn enter_assignment(&mut self, assignment: &yul::Assignment) {
        self.statement_acc.push(yul::Statement::Assignment(assignment.clone()));
    }
    fn enter_expression(&mut self, expression: &yul::Expression) {
        self.statement_acc.push(yul::Statement::Expression(expression.clone()));
    }

    fn visit_if(&mut self, ifs: &yul::If) {
        self.save_acc();

        let header = self.new_node();
        let true_branch = self.new_node();
        let after_if = self.new_node();

        self.connect(self.current.clone(), header.clone(), Edge::IfHeader);
        self.connect(
            header.clone(),
            true_branch.clone(),
            Edge::IfTrueBranch(ifs.condition.clone()),
        );
        self.connect(
            header,
            after_if.clone(),
            Edge::IfFalseBranch(ifs.condition.clone()),
        );
        self.connect(
            true_branch.clone(),
            after_if.clone(),
            Edge::AfterIf,
        );

        self.set_current(true_branch);

        self.visit_block(&ifs.body);

        self.save_acc();

        self.set_current(after_if);
    }

    fn visit_switch(&mut self, switch: &yul::Switch) {
        self.save_acc();

        let header = self.new_node();
        let after = self.new_node();

        self.connect(self.current.clone(), header.clone(), Edge::LoopHeader);
        self.connect(header.clone(), after.clone(), Edge::AfterSwitch);

        switch.cases.iter().for_each(|case| {
            let case_node = self.new_node();
            self.connect(
                header.clone(),
                case_node.clone(),
                Edge::SwitchCase(switch.expression.clone(), case.literal.clone()),
            );
            self.connect(case_node.clone(), after.clone(), Edge::AfterSwitch);

            self.set_current(case_node.clone());
            self.visit_block(&case.body);
            self.save_acc();
        });

        self.set_current(after);
    }

    fn visit_for(&mut self, for_loop: &yul::ForLoop) {
        self.statement_acc.append(&mut for_loop.pre.statements.clone());
        self.save_acc();

        let header = self.new_node();
        let body = self.new_node();
        let post = self.new_node();
        let after = self.new_node();

        self.connect(self.current.clone(), header.clone(), Edge::LoopHeader);
        self.connect(
            header.clone(),
            body.clone(),
            Edge::LoopBody(for_loop.condition.clone()),
        );
        self.connect(
            header.clone(),
            after.clone(),
            Edge::LoopFalse(for_loop.condition.clone()),
        );
        self.connect(body.clone(), post.clone(), Edge::LoopPost);
        self.connect(body.clone(), after.clone(), Edge::AfterLoop);
        self.connect(post.clone(), header.clone(), Edge::LoopBack);

        self.loops.push((header, after.clone()));

        self.set_current(body);
        self.visit_block(&for_loop.body);
        self.save_acc();

        self.set_current(post);
        self.visit_block(&for_loop.post);
        self.save_acc();

        // TODO make this work
        //self.loops.pop_back();
        self.set_current(after);
    }

    fn enter_break(&mut self) {
        self.save_acc();

        self.connect(
            self.current.clone(),
            self.loops.last().unwrap().1.clone(),
            Edge::Break,
        );

        let ghost = self.new_node();
        self.set_current(ghost);
        self.save_acc();
    }

    fn enter_continue(&mut self) {
        self.save_acc();

        self.connect(
            self.current.clone(),
            self.loops.last().unwrap().0.clone(),
            Edge::Continue,
        );

        let ghost = self.new_node();
        self.set_current(ghost);
        self.save_acc();
    }

    fn enter_leave(&mut self) {
        self.save_acc();

        self.connect(
            self.current.clone(),
            self.cfg
                .functions
                .get(self.fun_defs.last().unwrap())
                .unwrap()
                .1
                .clone(),
            Edge::Leave,
        );

        let ghost = self.new_node();
        self.set_current(ghost);
        self.save_acc();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yultsur::yul;
    use yultsur::yul_parser;

    #[test]
    fn yul_block() {
        let block = yul_parser::parse_block("{ let a := 2 }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_if_basic() {
        let block = yul_parser::parse_block("{ if 1 { } }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_if() {
        let block = yul_parser::parse_block("{ let a := 2 if a { a := 0 } let b := 666 }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    // TODO `switch` is actually buggy in the parser
    #[test]
    fn yul_switch_basic() {
        let block = yul_parser::parse_block("{ switch 3 case 0 { } default { } }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_for_basic() {
        let block = yul_parser::parse_block("{ for {} 1 {} {} }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_for() {
        let block = yul_parser::parse_block("{ let a := 2 for { a := 3 } a { a := 4 } { a := 5 } a := 6}");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_for_break_basic() {
        let block = yul_parser::parse_block("{ for {} 1 { break } {} }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn yul_for_continue_basic() {
        let block = yul_parser::parse_block("{ for {} 1 { continue } {} }");

        let cfg = CFGBuilder::build(yul::Statement::Block(block));

        println!("{:?}", cfg);
    }

    #[test]
    fn if_statement() {
        let if_st = yul::If {
            condition: yul::Expression::Literal(yul::Literal {
                literal: "cond".to_string(),
                yultype: None,
            }),
            body: yul::Block { statements: vec![] },
        };

        let cfg = CFGBuilder::build(yul::Statement::If(if_st));

        println!("{:?}", cfg);
    }
}