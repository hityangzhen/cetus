package cetus.analysis;

import cetus.hir.*;
import cetus.analysis.*;
import java.util.*;
import cetus.application.*;

// @author yangzhen 2015-12-14
public class LoopAnalysisPass extends AnalysisPass {

    public LoopAnalysisPass(Program program) {
        super(program);
    }

    private static final String pass_name = "[LoopAnalysis]";
    //loop count
    public int count=0;

    private class LabelMeta implements Comparable{
        public LabelMeta(Label l) {
            label=l;
            stmt_set=new HashSet<Statement>();
            goto_self=null;
        }

        public int compareTo(Object obj) {
            LabelMeta meta=(LabelMeta)obj;
            int curr_line=this.label.where();
            int meta_line=meta.label.where();
            return curr_line<meta_line?1:(curr_line>meta_line?-1:0);
        }
        public boolean inCyclicLabelRegion(Statement stmt) {
            if(stmt.where()<label.where() || stmt.where()>goto_self.where())
                return false;
            return true;
        }
        public Label label;
        public Set<Statement> stmt_set;
        public GotoStatement goto_self;
    }

    private Map<Label,LabelMeta> label_meta_map;
    private Map<Procedure,Set<LabelMeta>> proc_labelmetas_map;

    //assume that the cyclic label will goto self
    public void analyzeLabel(Procedure proc) {
        Set<LabelMeta> labelmetas=null;
        //traverse all label stmts
        DFIterator<Label> label_iter=new DFIterator<Label>(proc,Label.class);
        while(label_iter.hasNext()) {
            Label label=label_iter.next();
            LabelMeta meta=new LabelMeta(label);
            label_meta_map.put(label,meta);
            if(!proc_labelmetas_map.containsKey(proc)) {
                labelmetas=new TreeSet<LabelMeta>();
                labelmetas.add(meta);
                proc_labelmetas_map.put(proc,labelmetas);
            }else {
                labelmetas=proc_labelmetas_map.get(proc);
                labelmetas.add(meta);
            }
        }
        if(labelmetas==null)
            return ;
        //traverse all goto stmts
        DFIterator<GotoStatement> goto_iter=new DFIterator<GotoStatement>(proc,
            GotoStatement.class);
        while(goto_iter.hasNext()) {
            GotoStatement goto_stmt=goto_iter.next();
            for(LabelMeta meta:labelmetas) {
                //find the nearst label
                if(meta.label.where()<goto_stmt.where()) {
                    meta.stmt_set.add(goto_stmt);
                    if(goto_stmt.getTarget()==meta.label) {
                        //choose the farthest goto stmt
                        if(meta.goto_self==null || 
                            meta.goto_self.where()<goto_stmt.where())
                            meta.goto_self=goto_stmt;                        
                    }
                    break;
                }// if(meta.label.where()<goto_stmt.where())
            }// for(LabelMeta meta:labelmetas)
        }
        //traverse all return stmts
        DFIterator<ReturnStatement> rtn_iter=new DFIterator<ReturnStatement>(proc,
            ReturnStatement.class);
        while(rtn_iter.hasNext()) {
            ReturnStatement rtn_stmt=rtn_iter.next();
            for(LabelMeta meta:labelmetas) {
                //find the nearst label
                if(meta.label.where()<rtn_stmt.where()) {
                    meta.stmt_set.add(rtn_stmt);
                    break;
                }// if(meta.label.where()<rtn_stmt.where())
            }// for(LabelMeta meta:labelmetas) 
        }
    }

    //compute the exit conditions of loop
    public void analyzeLoop(Traversable loop) {
        Set<Expression> exiting_condtion=new HashSet<Expression>();
        //loop
        if(loop instanceof Loop) {
            CFGraph loop_cfg=new CFGraph(loop);
            //find exit node
            List<DFANode> exit_nodes=loop_cfg.getExitNodes();
            //System.out.println("==============loop exit nodes:"+exit_nodes.size());

            for(DFANode node : exit_nodes) {
                //potential exit node
                Set<DFANode> pred_nodes=pred_nodes=node.getPreds();
                for(DFANode pred_node:pred_nodes) { 
                    Expression cond=null;
                    //loop condition
                    //  while(i>j) | do{}while(i>j) | for(;i>j;)
                    if(pred_node.getData("ir") instanceof Expression) {
                        cond=(Expression)pred_node.getData("ir");
                        //keep the valid condition
                        if(valid(cond,loop)) {
                            exiting_condtion.add(cond); 
                        }
                    }

                    //break stmt exit the loop may be associated with if/else
                    Statement stmt=pred_node.getData("stmt");
                    if(stmt instanceof BreakStatement) {
                        //every branch region should be a compound statement
                        if(stmt.getParent() instanceof CompoundStatement) {
                            Traversable break_stmt_par=stmt.getParent();
                            //nearest if stmt
                            //some break stmt may be in else branch,this situation we also 
                            //consider the if-condition
                            if(break_stmt_par.getParent() instanceof IfStatement) {
                                IfStatement if_stmt=(IfStatement)break_stmt_par.getParent();
                                if(valid(if_stmt.getControlExpression(),loop)) {
                                    exiting_condtion.add(if_stmt.getControlExpression());
                                }
                            }// if(break_stmt_par.getParent() instanceof IfStatement)
                        }// if(stmt.getParent() instanceof CompoundStatement)
                    }// if(stmt instanceof BreakStatement)
                }// for(DFANode pred_node:pred_nodes)
            }// for(DFANode node : exit_nodes)

            //we assume that goto stmt corresponding label region not in loop
            //typically,we use the goto stmt in loop is to break the loop 
            DFIterator<GotoStatement> goto_iter=new DFIterator<GotoStatement>(
                loop,GotoStatement.class);
            while(goto_iter.hasNext()) {
                GotoStatement goto_stmt=goto_iter.next();
                if(goto_stmt.getParent() instanceof CompoundStatement) {
                    Traversable goto_stmt_par=goto_stmt.getParent();
                    //nearest if stmt
                    if(goto_stmt_par.getParent() instanceof IfStatement) {
                        IfStatement if_stmt=(IfStatement)goto_stmt_par.getParent();
                        if(valid(if_stmt.getControlExpression(),loop)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }
                    }// if(goto_stmt_par.getParent() instanceof IfStatement)
                }// if(goto_stmt.getParent() instanceof CompoundStatement)
            }// while(goto_iter.hasNext())

            //return stmt
            DFIterator<ReturnStatement> rtn_iter=new DFIterator<ReturnStatement>(
                loop,ReturnStatement.class);
            while(rtn_iter.hasNext()) {
                ReturnStatement rtn_stmt=rtn_iter.next();
                if(rtn_stmt.getParent() instanceof CompoundStatement) {
                    Traversable rtn_stmt_par=rtn_stmt.getParent();
                    //nearest if stmt
                    if(rtn_stmt_par.getParent() instanceof IfStatement) {
                        IfStatement if_stmt=(IfStatement)rtn_stmt_par.getParent();
                        if(valid(if_stmt.getControlExpression(),loop)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }
                    }
                }
            }            
        }// if(loop instanceof Loop) 
        else if(loop instanceof Label) {
            Set<Statement> stmt_set=label_meta_map.get((Label)loop).stmt_set;
            for(Statement stmt:stmt_set) {
                if(stmt.getParent() instanceof CompoundStatement) {
                    Traversable stmt_par=stmt.getParent();
                    //nearest if stmt
                    if(stmt_par.getParent() instanceof IfStatement) {
                        IfStatement if_stmt=(IfStatement)stmt_par.getParent();
                        if(valid(if_stmt.getControlExpression(),loop)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }
                    }// if(stmt_par.getParent() instanceof IfStatement)
                }// if(stmt.getParent() instanceof CompoundStatement)
            }// for(Statement stmt:stmt_set)
        }// if(loop instanceof Label)

        if(loop instanceof Loop)
            System.out.println("===============loop exiting condition:"+exiting_condtion.size());
        else if(loop instanceof Label)
            System.out.println("===============label exiting condition:"+exiting_condtion.size());
        count++;
    }


    //whether condition expression is valid or not
    public boolean valid(Expression expr,Traversable loop) {
        //valid symbs of expr
        Set<Symbol> valid_symb_set=new HashSet<Symbol>();
        //symbs of expr
        Set<Symbol> symb_set=SymbolTools.getAccessedSymbols(expr);
        //accumulate global symb
        for(Symbol s : symb_set) {
            if(SymbolTools.isGlobal(s))
                valid_symb_set.add(s);
        }
        //interprocedural point to analysis
        Statement stmt=null;
        if(expr.getStatement() instanceof CompoundStatement)
            stmt=(Statement)expr.getStatement().getParent();
        else
            stmt=expr.getStatement();
        if(!(IPPointsToAnalysis.getPointsToRelations(stmt) instanceof NullDomain) && 
            !(IPPointsToAnalysis.getPointsToRelations(stmt) instanceof PointsToDomain.Universe)) {
            PointsToDomain domain=(PointsToDomain)IPPointsToAnalysis.getPointsToRelations(stmt);
            //only consider the pointers
            for(Symbol s : symb_set) {
                if(!SymbolTools.isPointer(s))
                    continue;
                //ensure that the pointer points to a heap region
                for(PointsToRel rel : domain.get(s)) {
                    if( rel.getPointedToSymbol().toString().contains("calloc") ||
                        rel.getPointedToSymbol().toString().contains("malloc") ||
                        rel.getPointedToSymbol().toString().contains("realloc") ||
                        rel.getPointedToSymbol().toString().contains("valloc") ) {
                        valid_symb_set.add(s);
                    }
                }
            }
        }

        Traversable trav=loop;

        //find the innnermost scope
        if(loop instanceof Label) {
            //label's parent is the compound stmt that only contain label and the 
            //first stmt next to label
            trav=loop.getParent().getParent();
        }

        //eliminate some symbs locally modified or interprocedural modifier (
        // we only the called functions)
        DFIterator<UnaryExpression> unary_iter=new DFIterator<UnaryExpression>(trav,
            UnaryExpression.class);
        while(unary_iter.hasNext()) {
            UnaryExpression sub_expr=unary_iter.next();
            if(loop instanceof Label) {
                //not in cyclic label region
                LabelMeta meta=label_meta_map.get((Label)loop);
                if(!meta.inCyclicLabelRegion(sub_expr.getStatement()))
                    continue;
            }
            validUnaryExpression(sub_expr,valid_symb_set);
        }

        DFIterator<AssignmentExpression> assign_iter=new DFIterator<AssignmentExpression>(
            trav,AssignmentExpression.class);
        while(assign_iter.hasNext()) {
            AssignmentExpression sub_expr=assign_iter.next();
            if(loop instanceof Label) {
                //not in cyclic label region
                LabelMeta meta=label_meta_map.get((Label)loop);
                if(!meta.inCyclicLabelRegion(sub_expr.getStatement()))
                    continue;
            }
            validAssignmentExpression(sub_expr,valid_symb_set);
        }

        DFIterator<FunctionCall> func_iter=new DFIterator<FunctionCall>(trav,
            FunctionCall.class);
        while(func_iter.hasNext()) {
            FunctionCall sub_expr=func_iter.next();
            if(loop instanceof Label) {
                //not in cyclic label region
                LabelMeta meta=label_meta_map.get((Label)loop);
                if(!meta.inCyclicLabelRegion(sub_expr.getStatement()))
                    continue;
            }
            validFunctionCall(sub_expr,valid_symb_set);
        }

        return !valid_symb_set.isEmpty();
    }

    void validUnaryExpression(Expression expr,Set<Symbol> valid_symb_set) {
        //indicate pre++,post++,pre--,post-- operators
        if(UnaryOperator.hasSideEffects(((UnaryExpression)expr).getOperator())) {
            Expression unary=(UnaryExpression)expr;
            Set<Symbol> sub_symbs=SymbolTools.getAccessedSymbols(unary);
            //we assume that unary-expr's operand is single symbol
            Symbol sub_symb=sub_symbs.iterator().next();
            Iterator<Symbol> iter=valid_symb_set.iterator();
            while(iter.hasNext()) {
                Symbol valid_symb=iter.next();
                if(valid_symb.getSymbolName().contains(sub_symb.getSymbolName()))
                    iter.remove();          
            }
        }
    }

    void validAssignmentExpression(Expression expr,Set<Symbol> valid_symb_set) {
        //indicate the lefthand value
        Expression lhs=((AssignmentExpression)expr).getLHS();
        Set<Symbol> sub_symbs=SymbolTools.getAccessedSymbols(lhs);
        Symbol sub_symb=sub_symbs.iterator().next();
        Iterator<Symbol> iter=valid_symb_set.iterator();
        while(iter.hasNext()) {
            Symbol valid_symb=iter.next();
            if(valid_symb.getSymbolName().contains(sub_symb.getSymbolName()))
                iter.remove();          
        }
    }

    void validFunctionCall(Expression expr,Set<Symbol> valid_symb_set) {
        //filter some symbs modified in called functions
        FunctionCall func_call=(FunctionCall)expr;
        Procedure proc=func_call.getProcedure();
        //def array of the called function
        AnalysisTarget[] defTargetArray = IPChainAnalysis.ipchain_analysis.getDefTargetArray(proc);
        //use array of the called function
        AnalysisTarget[] useTargetArray = IPChainAnalysis.ipchain_analysis.getUseTargetArray(proc);
        //if the pointer is passed to the called function
        //we assume that global variable will not be passed to called function by argument list
        List<Expression> arguments=func_call.getArguments();
        for(Symbol valid_symb : valid_symb_set) {
            //keep the index of parameters
            int argum_index=0;
            //use the corresponding param as the root def
            for(Expression argument:arguments) {
                //passed to the called function
                if(SymbolTools.getAccessedSymbols(argument).contains(valid_symb)) {
                    System.out.println("==============passed argument:"+argument);
                    //get the use list in the called function
                    AnalysisTarget def_target=defTargetArray[argum_index];
                    List<Traversable> use_list=IPChainAnalysis.ipchain_analysis.getUseList(
                        def_target.getExpression());
                    System.out.println("==============use list:"+use_list);
                    for(Traversable use:use_list) {
                        //traverse all expressions
                        DFIterator<Expression> use_iter=new DFIterator<Expression>(use,
                            Expression.class);
                        while(use_iter.hasNext()) {
                            Expression use_expr=(Expression)use_iter.next();
                            if(use_expr instanceof UnaryExpression) {
                                validUnaryExpression(use_expr,valid_symb_set);                                    
                            }
                            else if(use_expr instanceof AssignmentExpression) {                                 
                                validAssignmentExpression(use_expr,valid_symb_set);
                            }
                        }// while(use_iter.hasNext())
                    }// for(Traversable use:use_list)
                }// if(SymbolTools.getAccessedSymbols(argument).contains(valid_symb))
                argum_index++;
            }// for(Expression argument:arguments)
            System.out.println("===============valid set after passed argu analysis:"+
                valid_symb_set.size());

            //if directly modify global varibale in called function
            if(SymbolTools.isGlobal(valid_symb)) {
                //traverse def list instead of use list
                for(AnalysisTarget def_target:defTargetArray) {
                    Expression def_expr=def_target.getExpression();
                    //
                    if(SymbolTools.getAccessedSymbols(def_expr).contains(valid_symb)) {
                        Set<Symbol> sub_symbs=SymbolTools.getAccessedSymbols(def_expr);
                        Symbol sub_symb=sub_symbs.iterator().next();
                        Iterator<Symbol> symb_iter=valid_symb_set.iterator();
                        while(symb_iter.hasNext()) {
                            Symbol symb=symb_iter.next();
                            if(symb.getSymbolName().contains(sub_symb.getSymbolName()))
                                symb_iter.remove();          
                        }// while(symb_iter.hasNext())
                    }// if(SymbolTools.getAccessedSymbols(def_expr).contains(valid_symb))
                }// for(AnalysisTarget def_target:defTargetArray)
            }// if(SymbolTools.isGlobal(valid_symb))
            System.out.println("===============valid set after global analysis:"+
                valid_symb_set.size());
        }// for(Symbol valid_symb : valid_symb_set)
    }

    public String getPassName() {
        return pass_name;
    }

    public void start() {
        IPChainAnalysis.compute(program);
        label_meta_map=new HashMap<Label,LabelMeta>();
        proc_labelmetas_map=new HashMap<Procedure,Set<LabelMeta>>(); 
        //find cyclic label
        DFIterator<Procedure> proc_iter=new DFIterator<Procedure>(program,Procedure.class);
        while (proc_iter.hasNext()) {
            analyzeLabel(proc_iter.next());
        }
        //analysis loop
        DFIterator<Loop> loop_iter=new DFIterator<Loop>(program, Loop.class);
        while (loop_iter.hasNext()) {
            analyzeLoop(loop_iter.next());
        }
        for(LabelMeta meta:label_meta_map.values()) {
            if(meta.goto_self!=null)
                analyzeLoop(meta.label);
        }
        System.out.println("loop count:"+count);
    }
}
