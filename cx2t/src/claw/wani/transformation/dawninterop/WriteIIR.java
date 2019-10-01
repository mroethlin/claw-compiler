package claw.wani.transformation.dawninterop;

import claw.shenron.transformation.Transformation;
import claw.shenron.translator.Translator;
import claw.tatsu.xcodeml.xnode.common.*;
import claw.tatsu.xcodeml.xnode.fortran.FbasicType;
import claw.tatsu.xcodeml.xnode.fortran.FfunctionDefinition;
import claw.wani.transformation.ClawTransformation;
import dawn.proto.iir.IIROuterClass;
import dawn.proto.statements.Statements;

import java.io.FileOutputStream;
import java.util.*;

import static claw.tatsu.xcodeml.xnode.Xname.*;

public class WriteIIR extends ClawTransformation {

    private class UUID {
        private int curId = 0;
        public int nextId() {
            int ret = curId;
            curId++;
            return ret;
        }
    }

    private UUID uuid = new UUID();

    //global maps needed for meta information
    private HashMap<Integer, Integer> exprIDToAccessID_ = new HashMap<Integer, Integer>();
    private HashMap<Integer, String>  literalIDToName_  = new HashMap<Integer, String>();
    private HashMap<Integer, String>  accessIDToName_   = new HashMap<Integer, String>();
    private HashMap<String, Integer>  nameToAccessID_   = new HashMap<String, Integer>();

    //maps to update extents, those are local to a statement access pair, reset after each traversal
    private HashMap<Integer, Extents> fieldIdToReadExtents_ = new HashMap<Integer, Extents>();
    private HashMap<Integer, Extents> fieldIdToWriteExtents_ = new HashMap<Integer, Extents>();

    //reconstruction of FieldAccessType in dawn
    //  TODO add to proto
    private enum FieldAccessType {
        FAT_GlobalVariable(0), // a global variable (i.e. not field with grid dimensiontality)
        FAT_Literal(1),        // a literal that is not stored in memory
        FAT_LocalVariable(2),
        FAT_StencilTemporary(3),
        FAT_InterStencilTemporary(4),
        FAT_Field(5),
        FAT_APIField(6);

        public final Integer label;

        private FieldAccessType(Integer label) {
            this.label = label;
        }
    }

    //reconstruction of BuiltInType in dawn
    //  TODO add to proto
    private enum BuiltInType {
        Invalid(0),
        Auto(1),
        Boolean(2),
        Integer(3),
        Float(4);

        public final Integer label;

        private BuiltInType(Integer label) {
            this.label = label;
        }
    }

    private class Extents {
        Integer iminus = 0, iplus = 0;
        Integer jminus = 0, jplus = 0;
        Integer kminus = 0, kplus = 0;
    }

    //entry points for processing
    //  filled in during analysis phase (analyze)
    private FfunctionDefinition fun_;
    private Xnode iloop_;
    private Xnode jloop_;
    private Xnode kloop_;

    public WriteIIR () { }

    /**
     * check whether the input file is suitable for dawn interoperability
     * current requirements:
     *      - only one function
     *      - this function contains exactly one triple loop
     *      - loop variables are called i, j and k, in this order
     *      - only the k loop is allowed to contain expressions
     */
    @Override
    public boolean analyze(XcodeProgram xcodeml, Translator translator) {
        int num_functions = 0;
        String fname = new String();

        //extract function
        for(Xnode child : xcodeml.getGlobalSymbolsTable().children()) {
            Xid id = new Xid(child);
            if (id.getSclass().compareTo(SCLASS_F_FUNC) == 0) {
                num_functions++;
            }
            fname = id.getName();
        }

        if (num_functions != 1) {
            return false;
        }

        XglobalDeclTable globalDeclarations = xcodeml.getGlobalDeclarationsTable();
        fun_ = globalDeclarations.getFunctionDefinition(fname);

        if (fun_.body().children().size() != 1) {
            return false;
        }

        //extract triple loop
        iloop_ = fun_.body().child(0);
        if (iloop_.body().children().size() != 1) {
            return false;
        }
        jloop_ = iloop_.body().child(0);
        if (jloop_.body().children().size() != 1) {
            return false;
        }
        kloop_ = jloop_.body().child(0);

        if (!Xnode.isOfCode(iloop_, Xcode.F_DO_STATEMENT)) {
            return false;
        }
        if (!Xnode.isOfCode(jloop_, Xcode.F_DO_STATEMENT)) {
            return false;
        }
        if (!Xnode.isOfCode(kloop_, Xcode.F_DO_STATEMENT)) {
            return false;
        }

        //check vars
        if (iloop_.matchDirectDescendant(Xcode.VAR).value().compareTo("i") != 0) {
            return false;
        }
        if (jloop_.matchDirectDescendant(Xcode.VAR).value().compareTo("j") != 0) {
            return false;
        }
        if (kloop_.matchDirectDescendant(Xcode.VAR).value().compareTo("k") != 0) {
            return false;
        }

        return true;
    }

    @Override
    public boolean canBeTransformedWith(XcodeProgram xcodeml, Transformation other) {
        return false;
    }


    private boolean isLeaf(Xnode node) {
        return Xnode.isOfCode(node, Xcode.F_ARRAY_REF) || Xnode.isOfCode(node, Xcode.F_REAL_CONSTANT) ||
                Xnode.isOfCode(node, Xcode.F_INT_CONSTANT);
    }

    private String ArrayNameFromArrayExprNode(Xnode node) {
        assert(node.opcode() == Xcode.F_ARRAY_REF);
        return node.children().get(0).children().get(0).value();
    }

    private boolean isConstant(Xnode node) {
        return node.opcode() == Xcode.F_INT_CONSTANT || node.opcode() == Xcode.F_REAL_CONSTANT;
    }

    private boolean isValidArrayIdx(Xnode node) {
        return node.value().compareTo("i") == 0 ||
               node.value().compareTo("j") == 0 ||
               node.value().compareTo("k") == 0;
    }

    private Integer idxFromString(String index) {
        if (index.compareTo("i") == 0) return 0;
        if (index.compareTo("j") == 0) return 1;
        if (index.compareTo("k") == 0) return 2;
        assert(false);
        return -1;
    }

    //update extents given a field id, i.e. "expand" the extents
    //  e.g (-1,+1) + (-2,0) => (-2,+1)
    private void updateExtents(int fieldID, Integer[] offsets, boolean read) {
        assert(offsets.length == 3);

        if (read) {
            if (!fieldIdToReadExtents_.containsKey(fieldID)) {
                fieldIdToReadExtents_.put(fieldID, new Extents());
            }
        } else {
            if (!fieldIdToWriteExtents_.containsKey(fieldID)) {
                fieldIdToWriteExtents_.put(fieldID, new Extents());
            }
        }

        Extents extents = (read) ? fieldIdToReadExtents_.get(fieldID) : fieldIdToWriteExtents_.get(fieldID);

        if (offsets[0] < 0) {
            extents.iminus = Math.min(offsets[0], extents.iminus);
        } else {
            extents.iplus  = Math.max(offsets[0], extents.iplus);
        }

        if (offsets[1] < 0) {
            extents.jminus = Math.min(offsets[1], extents.jminus);
        } else {
            extents.jplus  = Math.max(offsets[1], extents.jplus);
        }

        if (offsets[2] < 0) {
            extents.kminus = Math.min(offsets[2], extents.kminus);
        } else {
            extents.kplus  = Math.max(offsets[2], extents.kplus);
        }
    }

    //get offsets as an array from an array index xnode
    //  e.g. field(i+1,j-1,k+2) would return [1, -1, +2]
    private Integer[] offsetsFromArrayExprNode(Xnode node) {
        Integer[] offsets = new Integer[] {0, 0, 0};

        for (Xnode child : node.children()) {
            if (child.opcode() != Xcode.ARRAY_INDEX) continue;

            for (Xnode array_idx_child : child.children()) {
                if (array_idx_child.opcode() == Xcode.PLUS_EXPR || array_idx_child.opcode() == Xcode.MINUS_EXPR) {

                    Xnode binary_expr = array_idx_child;
                    Xnode left  = binary_expr.children().get(0);
                    Xnode right = binary_expr.children().get(1);

                    assert(isConstant(left) || isConstant(right));
                    assert(isValidArrayIdx(left) || isValidArrayIdx(right));

                    Xnode index  = isValidArrayIdx(left) ? left : right;
                    Xnode offset = isConstant(left) ? left : right;

                    Integer indexInt = idxFromString(index.value());
                    Integer offsetInt = Integer.parseInt(offset.value());
                    if (array_idx_child.opcode() == Xcode.MINUS_EXPR) offsetInt *= -1;

                    offsets[indexInt] = offsetInt;
                }
            }
        }
        return offsets;
    }

    //quick and stupid helper function to represent (some) opcodes by a String
    //  - opcode().ToString() does not work, returns stuff such as "F_ASSIGN_STATEMENT"
    private String opCodeStringFromBinaryExprNode(Xnode node) throws Exception {
        switch (node.opcode()) {
            case F_ASSIGN_STATEMENT:
                return "=";
            case PLUS_EXPR:
                return "+";
            case MINUS_EXPR:
                return "-";
            case MUL_EXPR:
                return "*";
            case DIV_EXPR:
                return "/";
            case LOG_AND_EXPR:
                return "&&";
            case LOG_OR_EXPR:
                return "||";
            case LOG_EQ_EXPR:
                return "==";
            case LOG_GE_EXPR:
                return ">=";
            case LOG_GT_EXPR:
                return ">";
            case LOG_LE_EXPR:
                return "<=";
            case LOG_LT_EXPR:
                return "<";
            default:
                throw new Exception("opcode not supported or not binary expression " + node.opcode().toString());
        }
    }

    //helper function that turns the extents class herein into dawn::proto extents
    private IIROuterClass.Extents iirExtentsFromExtents(Extents extents) {
        return IIROuterClass.Extents.newBuilder()
                .addExtents(IIROuterClass.Extent.newBuilder()
                        .setMinus(extents.iminus)
                        .setPlus(extents.iplus)
                        .build())
                .addExtents(IIROuterClass.Extent.newBuilder()
                        .setMinus(extents.jminus)
                        .setPlus(extents.jplus)
                        .build())
                .addExtents(IIROuterClass.Extent.newBuilder()
                        .setMinus(extents.kminus)
                        .setPlus(extents.kplus)
                        .build()).build();
    }

    //convert xnode leaf into dawn::protobuf field/literal expression
    //  I'm sure leafs can also be something else (like a function call)
    //  such cases simply assert to false
    private Statements.Expr exprFromLeaf(Xnode node, boolean read) {
        assert(isLeaf(node));

        Integer nextID = uuid.nextId();

        switch (node.opcode()) {
            case F_ARRAY_REF:
                String name = ArrayNameFromArrayExprNode(node);
                Integer[] offsets = offsetsFromArrayExprNode(node);
                Statements.FieldAccessExpr exprArrayRef = Statements.FieldAccessExpr.newBuilder()
                        .setID(nextID)
                        .setName(name)
                        .addAllOffset(Arrays.asList(offsets))
                        .build();
                String  fieldName = name;
                Integer fieldID = nameToAccessID_.get(fieldName);
                exprIDToAccessID_.put(nextID, fieldID);
                updateExtents(fieldID, offsets, read);
                return Statements.Expr.newBuilder().mergeFieldAccessExpr(exprArrayRef).build();
            case F_REAL_CONSTANT:
                String valueFloat = node.value();
                Statements.LiteralAccessExpr exprLiteralAccessFloat = Statements.LiteralAccessExpr.newBuilder()
                        .setID(-nextID)
                        .setValue(valueFloat)
                        .setType(Statements.BuiltinType.newBuilder().setTypeIdValue(BuiltInType.Float.label))
                        .build();
                literalIDToName_.put(-nextID, valueFloat);
                fieldIdToReadExtents_.put(-nextID, new Extents());
                return Statements.Expr.newBuilder().mergeLiteralAccessExpr(exprLiteralAccessFloat).build();
            case F_INT_CONSTANT:
                String valueInt = node.value();
                Statements.LiteralAccessExpr exprLiteralAccessInt = Statements.LiteralAccessExpr.newBuilder()
                        .setID(-nextID)
                        .setValue(valueInt)
                        .setType(Statements.BuiltinType.newBuilder().setTypeIdValue(BuiltInType.Integer.label))
                        .build();
                literalIDToName_.put(-nextID, valueInt);
                fieldIdToReadExtents_.put(-nextID, new Extents());
                return Statements.Expr.newBuilder().mergeLiteralAccessExpr(exprLiteralAccessInt).build();
            default:
                assert(false);
                return null;
        }
    }

    //convert xnode binary expression into dawn::protobuf binary expression
    private Statements.Expr BinaryExprFromNode(Xnode node, Statements.Expr left, Statements.Expr right) {
        assert(!isLeaf(node));
        try {
            Statements.BinaryOperator binOp = Statements.BinaryOperator.newBuilder()
                    .setID(uuid.nextId())
                    .setLeft(left)
                    .setRight(right)
                    .setOp(opCodeStringFromBinaryExprNode(node))
                    .build();
            return Statements.Expr.newBuilder().mergeBinaryOperator(binOp).build();
        } catch (Exception e) {
            System.out.println(e.getMessage());
            return null;
        }
    }

    //traverse AST tree in post order fashion
    //  - if expression is a leaf construct an access (literal of field)
    //  - otherwise expression is a binary expression with left hand side equal to the left hand subtree and vice versa
    private Statements.Expr traverse(Xnode node) {
        if (!isLeaf(node)) {
            Xnode left  = node.children().get(0);
            Xnode right = node.children().get(1);

            Statements.Expr left_tree  = traverse(left);
            Statements.Expr right_tree = traverse(right);

            return BinaryExprFromNode(node, left_tree, right_tree);
        } else {
            return exprFromLeaf(node, true);
        }
    }

    @Override
    public void transform(XcodeProgram xcodeml, Translator translator, Transformation other) throws Exception {

        // First, fill all the meta information, i.e. the following maps for simple examples
        // (there would be more for general examples)
        //
        //        1) accessIDToName
        //        2) exprIDToAccessID
        //        3) accessIDToType
        //        4) literalIDToName
        //        5) fieldAccessIDs
        //        6) APIFieldIDs
        //        7) fieldIDtoLegalDimensions
        //        8) stencil name
        //        9) idToStencilCall
        //
        // Most of them can be filled in by simply looking at the function params, which will translate to fields
        // some exceptions like exprIDToAccessID and literalIDToName can only be completed while looking at the actual
        // expressions contained in the innermost loop

        //we expect exactly one stencil generate ids for both the stencil itself and its decl call statement
        Integer stencilID = uuid.nextId();
        Integer stencilCallDeclStatementID = uuid.nextId();

        //this holds all the metainfo
        IIROuterClass.StencilMetaInfo.Builder iirMetaInfo = IIROuterClass.StencilMetaInfo.newBuilder();

        Statements.StencilCallDeclStmt stmt = Statements.StencilCallDeclStmt.newBuilder()
                .setID(stencilCallDeclStatementID)
                .setStencilCall(Statements.StencilCall.newBuilder().setCallee("__claw_generated__").build())
                .build();

        //idToStencilCall map (complete, 1/9)
        iirMetaInfo.putIdToStencilCall(stencilID,
                Statements.Stmt.newBuilder().mergeStencilCallDeclStmt(stmt).build());

        //extract all fields (= params) and fill maps
        for(Xnode child : fun_.getSymbolTable().children()) {
            Xid id = new Xid(child);
            if (id.getSclass().compareTo(SCLASS_F_PARAM)==0) {
                FbasicType param = xcodeml.getTypeTable().getBasicType(id.getType());
                String name = id.getName();

                int num_dimensions = param.getDimensions();
                assert(num_dimensions > 0 && num_dimensions <= 3);

                int fieldID = uuid.nextId();

                accessIDToName_.put(fieldID, name);
                nameToAccessID_.put(name, fieldID);

                iirMetaInfo.putAccessIDToName(fieldID, name);
                iirMetaInfo.addFieldAccessIDs(fieldID);
                iirMetaInfo.addAPIFieldIDs(fieldID);
                iirMetaInfo.putAccessIDToType(fieldID, FieldAccessType.FAT_APIField.label);
                iirMetaInfo.putFieldIDtoLegalDimensions(fieldID,
                        IIROuterClass.Array3i.newBuilder()
                                .setInt1(num_dimensions >= 1 ? 1 : 0)
                                .setInt2(num_dimensions >= 2 ? 1 : 0)
                                .setInt3(num_dimensions >= 3 ? 1 : 0)
                        .build());
            }
        }

        //AccessIDToName, FieldAccesssIDs, APIFieldIDs, AccessIDToType and FieldIdToLegalDimensions are now complete (6/9)

        //we have one stencil featuring one multistage holding one stage with one do method:
        IIROuterClass.IIR.Builder internalIIR = IIROuterClass.IIR.newBuilder();
        IIROuterClass.Stencil.Builder stencil = IIROuterClass.Stencil.newBuilder().setStencilID(stencilID);
        IIROuterClass.MultiStage.Builder multiStage = IIROuterClass.MultiStage.newBuilder().setMultiStageID(uuid.nextId());
        IIROuterClass.Stage.Builder stage = IIROuterClass.Stage.newBuilder().setStageID(uuid.nextId());
        IIROuterClass.DoMethod.Builder doMethod = IIROuterClass.DoMethod.newBuilder().setDoMethodID(uuid.nextId());

        //build actual statements, fill remaining maps
        for (Xnode child : kloop_.body().children()) {
            //I expect each top level to be an assign statement
            //      This is not necessarily true, I cant picture an example which is both simple and does not have this
            //      property, so its handled like this for now:
            assert(child.opcode() == Xcode.F_ASSIGN_STATEMENT);

            //traverse left (which should only be one statement)
            Statements.Expr expr_left  = exprFromLeaf(child.children().get(0), false);
            //traverse right (can be arbitrary AST tree)
            Statements.Expr expr_right = traverse(child.children().get(1));

            Statements.AssignmentExpr assignmentExpr = Statements.AssignmentExpr.newBuilder()
                    .setLeft(expr_left)
                    .setRight(expr_right)
                    .setOp(opCodeStringFromBinaryExprNode(child))
                    .setID(uuid.nextId())
                    .build();

            Statements.ExprStmt exprStmt = Statements.ExprStmt.newBuilder()
                    .mergeExpr(Statements.Expr.newBuilder().mergeAssignmentExpr(assignmentExpr).build()).build();

            //build statement access pair out of statement on the left (single) and on the right (arbitrary AST)
            IIROuterClass.StatementAccessPair.Builder stmtAccessPair = IIROuterClass.StatementAccessPair.newBuilder();
            stmtAccessPair.setASTStmt(Statements.Stmt.newBuilder().mergeExprStmt(exprStmt).build()).build();

            //build read and write extents
            IIROuterClass.Accesses.Builder accesses = IIROuterClass.Accesses.newBuilder();
            for (Map.Entry<Integer,Extents> entry : fieldIdToReadExtents_.entrySet()) {
                accesses.putReadAccess(entry.getKey(), iirExtentsFromExtents(entry.getValue()));
            }

            for (Map.Entry<Integer,Extents> entry : fieldIdToWriteExtents_.entrySet()) {
                accesses.putWriteAccess(entry.getKey(), iirExtentsFromExtents(entry.getValue()));
            }

            stmtAccessPair.setAccesses(accesses.build());
            doMethod.addStmtaccesspairs(stmtAccessPair.build());

            //extents are local to statement access pair and need to be cleared for each statement access pair
            fieldIdToReadExtents_.clear();
            fieldIdToWriteExtents_.clear();
        }

        //it wouldn't be too hard to support intervals which are not the full domain, for a simple
        //prototype we are assuming that k runs over the full domain (range of k in innermost for loop are in fact discarded)
        doMethod.setInterval(Statements.Interval.newBuilder()
                .setLowerOffset(0)
                .setUpperOffset(0)
                .setSpecialLowerLevel(Statements.Interval.SpecialLevel.Start)
                .setSpecialUpperLevel(Statements.Interval.SpecialLevel.End)
                . build()).build();

        //plug it all together
        stage.addDoMethods(doMethod.build()).build();
        multiStage.setLoopOrder(IIROuterClass.MultiStage.LoopOrder.Parallel);
        multiStage.addStages(stage).build();
        stencil.addMultiStages(multiStage).build();
        internalIIR.addControlFlowStatements(Statements.Stmt.newBuilder().mergeStencilCallDeclStmt(stmt).build());
        internalIIR.addStencils(stencil).build();

        //exprIdToAccess Map and literalIdToName map were filled by the traversal above,
        //lets store them in meta info (8/9)
        for (Map.Entry<Integer,Integer> entry : exprIDToAccessID_.entrySet()) {
            iirMetaInfo.putExprIDToAccessID(entry.getKey(), entry.getValue());
        }

        for (Map.Entry<Integer,String> entry : literalIDToName_.entrySet()) {
            iirMetaInfo.putLiteralIDToName(entry.getKey(), entry.getValue());
        }

        String inFname = xcodeml.getSource().substring(0, xcodeml.getSource().lastIndexOf('.'));
        String outFname = inFname + ".iir" + ".json";

        //final piece of meta info is the stencil name (9/9)
        iirMetaInfo.setStencilName(inFname);
        iirMetaInfo.build();

        //combine internal IR and meta data to arrive at the complete stencil instantiation
        IIROuterClass.StencilInstantiation iir = IIROuterClass.StencilInstantiation.newBuilder()
                .setMetadata(iirMetaInfo)
                .setInternalIR(internalIIR)
                .setFilename("__dawn_generated__")
                .build();

        //write json
        String jsonString = com.google.protobuf.util.JsonFormat.printer().
                includingDefaultValueFields().preservingProtoFieldNames().print(iir);

        FileOutputStream ostream = new FileOutputStream(outFname);
        ostream.write(jsonString.getBytes());
        ostream.flush();
    }

}
