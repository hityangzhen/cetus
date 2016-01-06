package cetus.analysis;

import cetus.hir.*;
import cetus.analysis.*;
import java.util.*;
import cetus.application.*;
import java.io.*;

// @author yangzhen 2015-12-14
public class LoopAnalysisPass extends AnalysisPass {

    public LoopAnalysisPass(Program program) {
        super(program);
    }

    private static final String pass_name = "[LoopAnalysis]";
    private static boolean cond_wait=true;
    //loop count
    private int count=0;

    private class ProcedureMeta {
        public ProcedureMeta(String source,int psl,int pel) {
            this.source=source;
            this.psl=psl;
            this.pel=pel;
        }
        public String source;
        public int psl;
        public int pel;
    }
    private class LoopMeta {
        public LoopMeta(ProcedureMeta pm,int lsl,int lel,Set<Expression> exprs) {
            this.pm=pm;
            this.lsl=lsl;
            this.lel=lel;
            this.exprs=exprs;
        }
        public ProcedureMeta pm;
        public int lsl;
        public int lel;
        //exiting condition exprs or data dependent exprs
        public Set<Expression> exprs;
    }

    private class LabelMeta implements Comparable{
        public LabelMeta(Label l) {
            label=l;
            stmt_set=new HashSet<Statement>();
            goto_self=null;
            cw_call=null;
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
        public FunctionCall cw_call;
    }

    private Map<Label,LabelMeta> label_meta_map;
    private Map<Procedure,Set<LabelMeta>> proc_labelmetas_map;
    private Map<Procedure,ProcedureMeta> proc_pm_map;
    private Set<LoopMeta> loop_meta_set;

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

        Iterator<LabelMeta> iter=labelmetas.iterator();
        while(iter.hasNext()) {
            LabelMeta meta=iter.next();
            if(meta.goto_self==null) {
                iter.remove();
                label_meta_map.remove(meta.label);                
            }
        }
        //
        if(cond_wait) {
            //traverse all func call stmts
            DFIterator<FunctionCall> fc_iter=new DFIterator<FunctionCall>(proc,
                FunctionCall.class);
            while(fc_iter.hasNext()) {
                FunctionCall fc=fc_iter.next();
                if(fc.toString().contains("cond_wait")) {
                    for(LabelMeta meta:labelmetas) {
                        //find the nearst label
                        if(meta.label.where()<fc.getStatement().where()) {
                            meta.cw_call=fc;
                            break;
                        }// if(meta.label.where()<fc.where()) {
                    }// for(LabelMeta meta:labelmetas)
                }
            }
            //filter the label loop doesn't contain cond_wait
            iter=labelmetas.iterator();
            while(iter.hasNext()) {
                LabelMeta meta=iter.next();
                if(meta.cw_call==null) {
                    iter.remove();
                    label_meta_map.remove(meta.label);                    
                }
            } 
        }
        //current procedure no apropriate label loops
        if(labelmetas.isEmpty()) {
            proc_labelmetas_map.remove(proc);
        }
    }

    //analysis the procedure scope
    public void analyzeProcedureScope(Procedure proc) {
        int proc_sl=0,proc_el=0;
        proc_sl=proc.getBody().where();
        String source=proc.getBody().getSource();
        //traverse the statements find the end line
        DFIterator<Statement> stmt_iter=new DFIterator<Statement>(proc,
            Statement.class);
        while(stmt_iter.hasNext()) {
            Statement stmt=stmt_iter.next();
            if(stmt.where()>proc_el)
                proc_el=stmt.where();
        }
        proc_pm_map.put(proc,new ProcedureMeta(source,proc_sl,proc_el));
    }

    //compute the exit conditions of loop
    public void analyzeLoop(Traversable loop) {
        Set<Expression> exiting_condtion=new HashSet<Expression>();
        int loop_sl=0,loop_el=0;
        //loop
        if(loop instanceof Loop) {
            //find the loop start line
            if(loop instanceof DoLoop || loop instanceof ForLoop ||
                loop instanceof WhileLoop)
                loop_sl=((Statement)loop).where();
            //traverse the statements find the end line
            DFIterator<Statement> stmt_iter=new DFIterator<Statement>(loop,
                Statement.class);
            while(stmt_iter.hasNext()) {
                Statement stmt=stmt_iter.next();
                if(stmt.where()>loop_el)
                    loop_el=stmt.where();
            }
            System.out.println("==========file name:"+((Statement)loop).getSource());
            System.out.println("==========loop start line:"+loop_sl);
            System.out.println("==========loop end line:"+loop_el);
            //cond_wait call
            FunctionCall cw_call=null;
            if(cond_wait) {
                DFIterator<FunctionCall> func_iter=new DFIterator<FunctionCall>(loop,
                    FunctionCall.class);
                while(func_iter.hasNext()) {
                    FunctionCall sub_expr=func_iter.next();
                    if(sub_expr.toString().contains("cond_wait")) {
                        cw_call=sub_expr;
                        break;
                    }
                }
                //filter the loop doesn't cantain cond_wait
                if(cw_call==null)
                    return ;
            }

            CFGraph loop_cfg=new CFGraph(loop);
            //find exit node
            List<DFANode> exit_nodes=loop_cfg.getExitNodes();
            System.out.println("==============loop exit nodes:"+exit_nodes.size());

            for(DFANode node : exit_nodes) {
                //goto stmt or return stmt will be as a exit node
                if(node.getData("stmt") instanceof GotoStatement ||
                    node.getData("stmt") instanceof ReturnStatement)
                    continue ;
                Set<DFANode> pred_nodes=pred_nodes=node.getPreds();
                //System.out.println("===============pred nodes:"+pred_nodes.size());
                for(DFANode pred_node:pred_nodes) {
                    //System.out.println("============pred node:"+pred_node);
                    Expression cond=null;
                    //loop condition
                    //  while(i>j) | do{}while(i>j) | for(;i>j;)
                    if(pred_node.getData("ir") instanceof Expression) {
                        cond=(Expression)pred_node.getData("ir");
                        //keep the valid condition
                        List<Expression> dd_exprs=new ArrayList<Expression>();
                        if(valid(cond,loop,dd_exprs)) {
                            exiting_condtion.add(cond); 
                        }else if(!dd_exprs.isEmpty()) {
                            exiting_condtion.add(dd_exprs.get(0));
                        }
                    }
                    System.out.println("=============exiting condition:"+exiting_condtion);
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
                                if(cond_wait) {
                                    int cw_line=cw_call.getStatement().where();
                                    int cond_line=if_stmt.getControlExpression().getStatement().where();
                                    if(cw_line<cond_line)
                                        continue;
                                }
                                List<Expression> dd_exprs=new ArrayList<Expression>();
                                System.out.println("==============if_stmt cond:"+if_stmt.getControlExpression());
                                if(valid(if_stmt.getControlExpression(),loop,dd_exprs)) {
                                    exiting_condtion.add(if_stmt.getControlExpression());
                                }else if(!dd_exprs.isEmpty()) {
                                    exiting_condtion.add(dd_exprs.get(0));
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
                //filter the goto target which is in the loop
                Label label=goto_stmt.getTarget();
                boolean valid_goto=true;
                DFIterator<Label> label_iter=new DFIterator<Label>(loop,Label.class);
                while(label_iter.hasNext()) {
                    Label l=label_iter.next();
                    if(l==label) {
                        valid_goto=false;
                        break;                        
                    }
                }
                if(valid_goto==false) {
                    continue;                    
                }

                if(goto_stmt.getParent() instanceof CompoundStatement) {
                    Traversable goto_stmt_par=goto_stmt.getParent();
                    //nearest if stmt
                    if(goto_stmt_par.getParent() instanceof IfStatement) {
                        IfStatement if_stmt=(IfStatement)goto_stmt_par.getParent();
                        if(cond_wait) {
                            int cw_line=cw_call.getStatement().where();
                            int cond_line=if_stmt.getControlExpression().getStatement().where();
                            if(cw_line<cond_line)
                                continue;
                        }
                        List<Expression> dd_exprs=new ArrayList<Expression>();
                        if(valid(if_stmt.getControlExpression(),loop,dd_exprs)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }else if(!dd_exprs.isEmpty()) {
                            exiting_condtion.add(dd_exprs.get(0));
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
                        if(cond_wait) {
                            int cw_line=cw_call.getStatement().where();
                            int cond_line=if_stmt.getControlExpression().getStatement().where();
                            if(cw_line<cond_line)
                                continue;
                        }
                        List<Expression> dd_exprs=new ArrayList<Expression>();
                        if(valid(if_stmt.getControlExpression(),loop,dd_exprs)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }else if(!dd_exprs.isEmpty()) {
                            exiting_condtion.add(dd_exprs.get(0));
                        }
                    }
                }
            }
        }// if(loop instanceof Loop) 
        else if(loop instanceof Label) {
            LabelMeta label_meta=label_meta_map.get((Label)loop);
            Set<Statement> stmt_set=label_meta.stmt_set;
            loop_sl=((Label)(loop)).where();
            loop_el=label_meta.goto_self.where();
            System.out.println("==========file name:"+((Label)loop).getSource());
            System.out.println("==========loop start line:"+loop_sl);
            System.out.println("==========loop end line:"+loop_el);
            for(Statement stmt:stmt_set) {
                if(stmt.getParent() instanceof CompoundStatement) {
                    Traversable stmt_par=stmt.getParent();
                    //nearest if stmt
                    if(stmt_par.getParent() instanceof IfStatement) {
                        IfStatement if_stmt=(IfStatement)stmt_par.getParent();
                        if(cond_wait) {
                            int cw_line=label_meta.cw_call.getStatement().where();
                            int cond_line=if_stmt.getControlExpression().getStatement().where();
                            if(cw_line<cond_line)
                                continue;
                        }
                        List<Expression> dd_exprs=new ArrayList<Expression>();
                        if(valid(if_stmt.getControlExpression(),loop,dd_exprs)) {
                            exiting_condtion.add(if_stmt.getControlExpression());
                        }else if(!dd_exprs.isEmpty()) {
                            exiting_condtion.add(dd_exprs.get(0));
                        }
                    }// if(stmt_par.getParent() instanceof IfStatement)
                }// if(stmt.getParent() instanceof CompoundStatement)
            }// for(Statement stmt:stmt_set)
        }// if(loop instanceof Label)

        //
        if(!exiting_condtion.isEmpty()) {
            Procedure proc=((Statement)loop).getProcedure();
            LoopMeta loop_meta=new LoopMeta(proc_pm_map.get(proc),loop_sl,loop_el,
                exiting_condtion);
            loop_meta_set.add(loop_meta);
        }

        if(loop instanceof Loop) {
            System.out.println("===============loop exiting condition:"+exiting_condtion.size());
            for(Expression e:exiting_condtion)
                System.out.println(e);            
        }
        else if(loop instanceof Label)
            System.out.println("===============label exiting condition:"+exiting_condtion.size());
        count++;
    }

    //whether the data dependent expr is valid or not
    public boolean dd_valid(Expression expr) {
         //valid symbs of expr
        Set<Symbol> valid_symb_set=new HashSet<Symbol>();
        //symbs of expr
        Set<Symbol> symb_set=SymbolTools.getAccessedSymbols(expr);
        boolean all_local=true;
        //accumulate global symb
        for(Symbol s : symb_set) {
            if(SymbolTools.isGlobal(s)) {
                valid_symb_set.add(s);
                all_local=false;                
            }
        }
        if(all_local)
            return false;

        //interprocedural point to analysis
        Statement stmt=null;
        if(expr.getStatement() instanceof CompoundStatement)
            stmt=(Statement)expr.getStatement().getParent();
        else
            stmt=expr.getStatement();
        try {
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
        }catch(Exception e) {
            //do nothing
            e.printStackTrace();
        }

        //eliminate some symbs locally modified or interprocedural modifier in the expr
        DFIterator<UnaryExpression> unary_iter=new DFIterator<UnaryExpression>(expr,
            UnaryExpression.class);
        while(unary_iter.hasNext()) {
            UnaryExpression sub_expr=unary_iter.next();
            validUnaryExpression(sub_expr,valid_symb_set);
        }

        return !valid_symb_set.isEmpty();
    }

    //whether condition expression is valid or not
    //if the symbols in condition are local, we will check the data dependency
    public boolean valid(Expression expr,Traversable loop,List<Expression> dd_exprs) {
        //valid symbs of expr
        Set<Symbol> valid_symb_set=new HashSet<Symbol>();
        //symbs of expr
        Set<Symbol> symb_set=SymbolTools.getAccessedSymbols(expr);
        
        boolean all_local=true;
        //accumulate global symb
        for(Symbol s : symb_set) {
            if(SymbolTools.isGlobal(s)) {
                valid_symb_set.add(s);
                all_local=false;                
            }
        }
        //all symbols are local
        if(all_local) {
            int line=expr.getStatement().where();
            DFIterator<AssignmentExpression> assign_iter=new DFIterator<AssignmentExpression>(
                loop,AssignmentExpression.class);
            while(assign_iter.hasNext()) {
                AssignmentExpression sub_expr=assign_iter.next();
                int new_line=sub_expr.getStatement().where();
                if(new_line>line)
                    continue;

                if(loop instanceof Label) {
                    //not in cyclic label region
                    LabelMeta meta=label_meta_map.get((Label)loop);
                    if(!meta.inCyclicLabelRegion(sub_expr.getStatement()))
                        continue;
                }
                //find the left handle expression
                Expression lhs=((AssignmentExpression)sub_expr).getLHS();
                Set<Symbol> sub_symbs=SymbolTools.getAccessedSymbols(lhs);
                Symbol sub_symb=sub_symbs.iterator().next();
                Iterator<Symbol> iter=symb_set.iterator();
                while(iter.hasNext()) {
                    Symbol local_symb=iter.next();
                    //find the local symb is the left hand of the assignment expression
                    if(sub_symb.getSymbolName().contains(local_symb.getSymbolName())) {
                        //we should check the right hand of expression
                        Expression rhs=((AssignmentExpression)sub_expr).getRHS();
                        if(dd_valid(rhs)) {
                            System.out.println("=======data dependence stmt:"+rhs.getStatement());
                            if(dd_exprs.isEmpty())
                                dd_exprs.add(sub_expr);
                            //we only keep the nearest data dependent expr
                            else {
                                int old_line=dd_exprs.get(0).getStatement().where();
                                if(old_line<new_line) {
                                    dd_exprs.remove(0);
                                    dd_exprs.add(sub_expr);
                                }
                            }                     
                        }// if(dd_valid(rhs))
                    }         
                }
            }// while(assign_iter.hasNext())
        }// if(all_local)

        //interprocedural point to analysis
        Statement stmt=null;
        if(expr.getStatement() instanceof CompoundStatement)
            stmt=(Statement)expr.getStatement().getParent();
        else
            stmt=expr.getStatement();
        try {
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
        }catch(Exception e) {
            //do nothing
            e.printStackTrace();
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

        // System.out.println("==========valid symbol set size:"+valid_symb_set.size());
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
            if(sub_expr.toString().contains("cond_wait"))
                continue;
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
        try {
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
                    // System.out.println("==============passed argument:"+argument);
                    //get the use list in the called function
                    AnalysisTarget def_target=defTargetArray[argum_index];
                    List<Traversable> use_list=IPChainAnalysis.ipchain_analysis.getUseList(
                        def_target.getExpression());
                    // System.out.println("==============use list:"+use_list);
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
            // System.out.println("===============valid set after passed argu analysis:"+
                // valid_symb_set.size());

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
            // System.out.println("===============valid set after global analysis:"+
                // valid_symb_set.size());
        }// for(Symbol valid_symb : valid_symb_set)
        }catch(Exception e) {
            e.printStackTrace();
        }
    }

    public void export() {
        String file_name=null;
        if(cond_wait)
            file_name="cond_wait_lines.out";
        else
            file_name="exiting_condtion_lines.out";
        try {
            FileWriter fw=new FileWriter(file_name,true);
            BufferedWriter bw=new BufferedWriter(fw);
            for(LoopMeta loop_meta:loop_meta_set) {
                String source=loop_meta.pm.source;
                StringBuilder sb=new StringBuilder();
                sb.append(source);
                sb.append(" ");
                sb.append(loop_meta.pm.psl);
                sb.append(" ");
                sb.append(loop_meta.pm.pel);
                sb.append(" ");
                sb.append(loop_meta.lsl);
                sb.append(" ");
                sb.append(loop_meta.lel);
                sb.append(" ");
                for(Expression expr:loop_meta.exprs) {
                    sb.append(expr.getStatement().where());
                    sb.append(" ");
                }
                bw.write(sb.toString());
                bw.newLine();
                bw.flush();
            }
            bw.close();
            fw.close();
        }
        catch(Exception e) {
            e.printStackTrace();
        }
    }

    public String getPassName() {
        return pass_name;
    }

    public void start() {
        IPChainAnalysis.compute(program);
        label_meta_map=new HashMap<Label,LabelMeta>();
        proc_labelmetas_map=new HashMap<Procedure,Set<LabelMeta>>(); 
        proc_pm_map=new HashMap<Procedure,ProcedureMeta>();
        loop_meta_set=new HashSet<LoopMeta>();
        //find cyclic label
        DFIterator<Procedure> proc_iter=new DFIterator<Procedure>(program,Procedure.class);
        while (proc_iter.hasNext()) {
            Procedure proc=proc_iter.next();
            analyzeLabel(proc);
            analyzeProcedureScope(proc);
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
        //
        export();
    }
}
