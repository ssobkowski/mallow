mod inliner;
pub mod walker;

use crate::ast::Block;
use inliner::Inliner;
use walker::AstRewriter;

trait Pass: AstRewriter {
    fn run(&mut self, block: Block) -> Block {
        self.rewrite_block(block)
    }
}

impl<T: AstRewriter> Pass for T {}

pub fn run_all(block: Block) -> Block {
    let mut inliner = Inliner::new();
    inliner.run(block)
}
