module {
  handshake.func @admm(%arg0: !handshake.channel<f32>, %arg1: memref<30xf32>, %arg2: memref<900xf32>, %arg3: memref<2xf32>, %arg4: memref<30xf32>, %arg5: memref<30xf32>, %arg6: memref<30xf32>, %arg7: memref<30xf32>, %arg8: memref<30xf32>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, %arg13: !handshake.control<>, %arg14: !handshake.control<>, %arg15: !handshake.control<>, %arg16: !handshake.control<>, %arg17: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["vdc", "inp", "KKT_inv", "out", "x", "z", "y", "rhs", "temp_x_tilde", "inp_start", "KKT_inv_start", "out_start", "x_start", "z_start", "y_start", "rhs_start", "temp_x_tilde_start", "start"], resNames = ["inp_end", "KKT_inv_end", "out_end", "x_end", "z_end", "y_end", "rhs_end", "temp_x_tilde_end", "end"]} {
    %0:4 = lsq[%arg8 : memref<30xf32>] (%arg16, %result_19, %addressResult_21, %dataResult_22, %result_35, %addressResult_37, %result_39, %addressResult_45, %dataResult_46, %result_65, %addressResult_67, %addressResult_73, %result_127)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %1:4 = lsq[%arg7 : memref<30xf32>] (%arg15, %result, %addressResult_3, %dataResult_4, %result_39, %addressResult_43, %result_97, %addressResult_105, %dataResult_106, %result_127, %addressResult_129, %addressResult_133, %result_127)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %2:4 = lsq[%arg6 : memref<30xf32>] (%arg14, %result, %addressResult_9, %dataResult_10, %result_65, %addressResult_77, %addressResult_81, %addressResult_83, %dataResult_84, %result_97, %addressResult_103, %result_127)  {groupSizes = [1 : i32, 3 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %3:3 = lsq[%arg5 : memref<30xf32>] (%arg13, %result, %addressResult_7, %dataResult_8, %result_65, %addressResult_75, %addressResult_79, %dataResult_80, %result_97, %addressResult_101, %result_127)  {groupSizes = [1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %4:3 = lsq[%arg4 : memref<30xf32>] (%arg12, %result, %addressResult_5, %dataResult_6, %result_65, %addressResult_69, %addressResult_71, %dataResult_72, %result_97, %addressResult_99, %result_127)  {groupSizes = [1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq4"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %memEnd = mem_controller[%arg3 : memref<2xf32>] %arg11 (%196, %addressResult_131, %dataResult_132, %addressResult_135, %dataResult_136) %result_127 {connectedBlocks = [10 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<900xf32>] %arg10 (%addressResult_41) %result_127 {connectedBlocks = [6 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<30xf32>] %arg9 (%addressResult) %result_127 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %5 = constant %arg17 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %6 = br %5 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %7 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %8 = br %arg17 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %9 = mux %index [%6, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%7, %trueResult_11] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%8, %trueResult_13]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant16", value = 30 : i32} : <>, <i32>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %15 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant18", value = 0.000000e+00 : f32} : <>, <f32>
    %16 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%17] %outputs_1 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %18 = negf %dataResult {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "negf0"} : <f32>
    %19 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %20 = trunci %19 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_3, %dataResult_4 = store[%20] %18 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store22", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <f32>, <i32>, <f32>
    %21 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %22 = trunci %21 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = store[%22] %15 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <f32>, <i32>, <f32>
    %23 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %24 = trunci %23 {handshake.bb = 1 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = store[%24] %15 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store16", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <f32>, <i32>, <f32>
    %25 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %26 = trunci %25 {handshake.bb = 1 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_9, %dataResult_10 = store[%26] %15 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store18", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <f32>, <i32>, <f32>
    %27 = addi %9, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %28 = cmpi ult, %27, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %28, %27 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %28, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_13, %falseResult_14 = cond_br %28, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %29 = merge %falseResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant19", value = 5.000000e-01 : f32} : <>, <f32>
    %32 = constant %result_15 {handshake.bb = 2 : ui32, handshake.name = "constant20", value = 0 : i32} : <>, <i32>
    %33 = mulf %29, %31 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %34 = negf %33 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "negf1"} : <f32>
    %35 = br %32 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %36 = br %33 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <f32>
    %37 = br %34 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <f32>
    %38 = br %result_15 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <>
    %39 = mux %index_18 [%35, %trueResult_119] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %40 = mux %index_18 [%36, %trueResult_121] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %41 = mux %index_18 [%37, %trueResult_123] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %result_17, %index_18 = control_merge [%38, %trueResult_125]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %42 = constant %result_17 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 0 : i32} : <>, <i32>
    %43 = br %42 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i32>
    %44 = br %40 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <f32>
    %45 = br %41 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <f32>
    %46 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i32>
    %47 = br %result_17 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <>
    %48 = mux %index_20 [%43, %trueResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %index_20 [%44, %trueResult_25] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %50 = mux %index_20 [%45, %trueResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<f32>, <f32>] to <f32>
    %51 = mux %index_20 [%46, %trueResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_19, %index_20 = control_merge [%47, %trueResult_31]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %52 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %53 = constant %52 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 30 : i32} : <>, <i32>
    %54 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %55 = constant %54 {handshake.bb = 4 : ui32, handshake.name = "constant23", value = 1 : i32} : <>, <i32>
    %56 = constant %result_19 {handshake.bb = 4 : ui32, handshake.name = "constant24", value = 0.000000e+00 : f32} : <>, <f32>
    %57 = constant %result_19 {handshake.bb = 4 : ui32, handshake.name = "constant25", value = 0 : i32} : <>, <i32>
    %58 = extui %48 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %59 = trunci %58 {handshake.bb = 4 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_21, %dataResult_22 = store[%59] %56 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <f32>, <i32>, <f32>
    %60 = addi %48, %55 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i32>
    %61 = cmpi ult, %60, %53 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_23, %falseResult_24 = cond_br %61, %60 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_25, %falseResult_26 = cond_br %61, %49 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    %trueResult_27, %falseResult_28 = cond_br %61, %50 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <f32>
    %trueResult_29, %falseResult_30 = cond_br %61, %51 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_31, %falseResult_32 = cond_br %61, %result_19 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_33, %falseResult_34 = cond_br %61, %57 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %62 = mux %index_36 [%falseResult_34, %trueResult_85] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %63 = mux %index_36 [%falseResult_26, %trueResult_87] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<f32>, <f32>] to <f32>
    %64 = mux %index_36 [%falseResult_28, %trueResult_89] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %65 = mux %index_36 [%falseResult_30, %trueResult_91] {handshake.bb = 5 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_35, %index_36 = control_merge [%falseResult_32, %trueResult_93]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %66 = constant %result_35 {handshake.bb = 5 : ui32, handshake.name = "constant26", value = 0 : i32} : <>, <i32>
    %67 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %68 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %69 = trunci %68 {handshake.bb = 5 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_37, %dataResult_38 = load[%69] %0#0 {handshake.bb = 5 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %70 = br %66 {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i32>
    %71 = br %dataResult_38 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <f32>
    %72 = br %63 {handshake.bb = 5 : ui32, handshake.name = "br18"} : <f32>
    %73 = br %64 {handshake.bb = 5 : ui32, handshake.name = "br19"} : <f32>
    %74 = br %65 {handshake.bb = 5 : ui32, handshake.name = "br20"} : <i32>
    %75 = br %62 {handshake.bb = 5 : ui32, handshake.name = "br21"} : <i32>
    %76 = br %67 {handshake.bb = 5 : ui32, handshake.name = "br22"} : <i64>
    %77 = br %68 {handshake.bb = 5 : ui32, handshake.name = "br23"} : <i64>
    %78 = br %result_35 {handshake.bb = 5 : ui32, handshake.name = "br24"} : <>
    %79 = mux %index_40 [%70, %trueResult_47] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %80 = mux %index_40 [%71, %trueResult_49] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<f32>, <f32>] to <f32>
    %81 = mux %index_40 [%72, %trueResult_51] {handshake.bb = 6 : ui32, handshake.name = "mux15"} : <i1>, [<f32>, <f32>] to <f32>
    %82 = mux %index_40 [%73, %trueResult_53] {handshake.bb = 6 : ui32, handshake.name = "mux16"} : <i1>, [<f32>, <f32>] to <f32>
    %83 = mux %index_40 [%74, %trueResult_55] {handshake.bb = 6 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %84 = mux %index_40 [%75, %trueResult_57] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %85 = mux %index_40 [%76, %trueResult_59] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<i64>, <i64>] to <i64>
    %86 = mux %index_40 [%77, %trueResult_61] {handshake.bb = 6 : ui32, handshake.name = "mux20"} : <i1>, [<i64>, <i64>] to <i64>
    %result_39, %index_40 = control_merge [%78, %trueResult_63]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %87 = source {handshake.bb = 6 : ui32, handshake.name = "source5"} : <>
    %88 = constant %87 {handshake.bb = 6 : ui32, handshake.name = "constant27", value = 30 : i32} : <>, <i32>
    %89 = source {handshake.bb = 6 : ui32, handshake.name = "source6"} : <>
    %90 = constant %89 {handshake.bb = 6 : ui32, handshake.name = "constant28", value = 1 : i32} : <>, <i32>
    %91 = source {handshake.bb = 6 : ui32, handshake.name = "source7"} : <>
    %92 = constant %91 {handshake.bb = 6 : ui32, handshake.name = "constant29", value = 4 : i64} : <>, <i64>
    %93 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %94 = constant %93 {handshake.bb = 6 : ui32, handshake.name = "constant30", value = 3 : i64} : <>, <i64>
    %95 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %96 = constant %95 {handshake.bb = 6 : ui32, handshake.name = "constant31", value = 2 : i64} : <>, <i64>
    %97 = source {handshake.bb = 6 : ui32, handshake.name = "source10"} : <>
    %98 = constant %97 {handshake.bb = 6 : ui32, handshake.name = "constant32", value = 1 : i64} : <>, <i64>
    %99 = extui %79 {handshake.bb = 6 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %100 = shli %85, %98 {handshake.bb = 6 : ui32, handshake.name = "shli0"} : <i64>
    %101 = shli %85, %96 {handshake.bb = 6 : ui32, handshake.name = "shli1"} : <i64>
    %102 = addi %100, %101 {handshake.bb = 6 : ui32, handshake.name = "addi7"} : <i64>
    %103 = shli %85, %94 {handshake.bb = 6 : ui32, handshake.name = "shli2"} : <i64>
    %104 = shli %85, %92 {handshake.bb = 6 : ui32, handshake.name = "shli3"} : <i64>
    %105 = addi %103, %104 {handshake.bb = 6 : ui32, handshake.name = "addi8"} : <i64>
    %106 = addi %102, %105 {handshake.bb = 6 : ui32, handshake.name = "addi9"} : <i64>
    %107 = addi %106, %99 {handshake.bb = 6 : ui32, handshake.name = "addi2"} : <i64>
    %108 = trunci %107 {handshake.bb = 6 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_41, %dataResult_42 = load[%108] %outputs {handshake.bb = 6 : ui32, handshake.name = "load7"} : <i32>, <f32>, <i32>, <f32>
    %109 = extui %79 {handshake.bb = 6 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %110 = trunci %109 {handshake.bb = 6 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_43, %dataResult_44 = load[%110] %1#0 {handshake.bb = 6 : ui32, handshake.name = "load8"} : <i32>, <f32>, <i32>, <f32>
    %111 = mulf %dataResult_42, %dataResult_44 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf1"} : <f32>
    %112 = addf %80, %111 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf0"} : <f32>
    %113 = trunci %86 {handshake.bb = 6 : ui32, handshake.name = "index_cast9"} : <i64> to <i32>
    %addressResult_45, %dataResult_46 = store[%113] %112 {handshake.bb = 6 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : <i32>, <f32>, <i32>, <f32>
    %114 = addi %79, %90 {handshake.bb = 6 : ui32, handshake.name = "addi3"} : <i32>
    %115 = cmpi ult, %114, %88 {handshake.bb = 6 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_47, %falseResult_48 = cond_br %115, %114 {handshake.bb = 6 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_49, %falseResult_50 = cond_br %115, %112 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    %trueResult_51, %falseResult_52 = cond_br %115, %81 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <f32>
    %trueResult_53, %falseResult_54 = cond_br %115, %82 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_55, %falseResult_56 = cond_br %115, %83 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_57, %falseResult_58 = cond_br %115, %84 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_59, %falseResult_60 = cond_br %115, %85 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i64>
    %trueResult_61, %falseResult_62 = cond_br %115, %86 {handshake.bb = 6 : ui32, handshake.name = "cond_br22"} : <i1>, <i64>
    %trueResult_63, %falseResult_64 = cond_br %115, %result_39 {handshake.bb = 6 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %116 = merge %falseResult_52 {handshake.bb = 7 : ui32, handshake.name = "merge1"} : <f32>
    %117 = merge %falseResult_54 {handshake.bb = 7 : ui32, handshake.name = "merge2"} : <f32>
    %118 = merge %falseResult_56 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <i32>
    %119 = merge %falseResult_58 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <i32>
    %result_65, %index_66 = control_merge [%falseResult_64]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    %120 = source {handshake.bb = 7 : ui32, handshake.name = "source11"} : <>
    %121 = constant %120 {handshake.bb = 7 : ui32, handshake.name = "constant33", value = 1.000000e-01 : f32} : <>, <f32>
    %122 = source {handshake.bb = 7 : ui32, handshake.name = "source12"} : <>
    %123 = constant %122 {handshake.bb = 7 : ui32, handshake.name = "constant34", value = 1.000000e+01 : f32} : <>, <f32>
    %124 = source {handshake.bb = 7 : ui32, handshake.name = "source13"} : <>
    %125 = constant %124 {handshake.bb = 7 : ui32, handshake.name = "constant35", value = -6.000000e-01 : f32} : <>, <f32>
    %126 = source {handshake.bb = 7 : ui32, handshake.name = "source14"} : <>
    %127 = constant %126 {handshake.bb = 7 : ui32, handshake.name = "constant36", value = 30 : i32} : <>, <i32>
    %128 = source {handshake.bb = 7 : ui32, handshake.name = "source15"} : <>
    %129 = constant %128 {handshake.bb = 7 : ui32, handshake.name = "constant37", value = 1 : i32} : <>, <i32>
    %130 = constant %result_65 {handshake.bb = 7 : ui32, handshake.name = "constant38", value = 0 : i32} : <>, <i32>
    %131 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %132 = trunci %131 {handshake.bb = 7 : ui32, handshake.name = "index_cast10"} : <i64> to <i32>
    %addressResult_67, %dataResult_68 = load[%132] %0#1 {handshake.bb = 7 : ui32, handshake.name = "load10"} : <i32>, <f32>, <i32>, <f32>
    %133 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %134 = trunci %133 {handshake.bb = 7 : ui32, handshake.name = "index_cast11"} : <i64> to <i32>
    %addressResult_69, %dataResult_70 = load[%134] %4#0 {handshake.bb = 7 : ui32, handshake.name = "load11"} : <i32>, <f32>, <i32>, <f32>
    %135 = mulf %dataResult_70, %125 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf2"} : <f32>
    %136 = addf %dataResult_68, %135 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf1"} : <f32>
    %137 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %138 = trunci %137 {handshake.bb = 7 : ui32, handshake.name = "index_cast12"} : <i64> to <i32>
    %addressResult_71, %dataResult_72 = store[%138] %136 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store12"} : <i32>, <f32>, <i32>, <f32>
    %139 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %140 = trunci %139 {handshake.bb = 7 : ui32, handshake.name = "index_cast13"} : <i64> to <i32>
    %addressResult_73, %dataResult_74 = load[%140] %0#2 {handshake.bb = 7 : ui32, handshake.name = "load13"} : <i32>, <f32>, <i32>, <f32>
    %141 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui14"} : <i32> to <i64>
    %142 = trunci %141 {handshake.bb = 7 : ui32, handshake.name = "index_cast14"} : <i64> to <i32>
    %addressResult_75, %dataResult_76 = load[%142] %3#0 {handshake.bb = 7 : ui32, handshake.name = "load14"} : <i32>, <f32>, <i32>, <f32>
    %143 = mulf %dataResult_76, %125 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf3"} : <f32>
    %144 = addf %dataResult_74, %143 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf2"} : <f32>
    %145 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui15"} : <i32> to <i64>
    %146 = trunci %145 {handshake.bb = 7 : ui32, handshake.name = "index_cast15"} : <i64> to <i32>
    %addressResult_77, %dataResult_78 = load[%146] %2#0 {handshake.bb = 7 : ui32, handshake.name = "load15"} : <i32>, <f32>, <i32>, <f32>
    %147 = mulf %dataResult_78, %123 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf4"} : <f32>
    %148 = addf %144, %147 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf3"} : <f32>
    %149 = cmpf olt, %148, %117 {handshake.bb = 7 : ui32, handshake.name = "cmpf0"} : <f32>
    %150 = cmpf ogt, %148, %116 {handshake.bb = 7 : ui32, handshake.name = "cmpf1"} : <f32>
    %151 = select %150[%116, %148] {handshake.bb = 7 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %152 = select %149[%117, %151] {handshake.bb = 7 : ui32, handshake.name = "select1"} : <i1>, <f32>
    %153 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui16"} : <i32> to <i64>
    %154 = trunci %153 {handshake.bb = 7 : ui32, handshake.name = "index_cast16"} : <i64> to <i32>
    %addressResult_79, %dataResult_80 = store[%154] %152 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store16"} : <i32>, <f32>, <i32>, <f32>
    %155 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui17"} : <i32> to <i64>
    %156 = trunci %155 {handshake.bb = 7 : ui32, handshake.name = "index_cast17"} : <i64> to <i32>
    %addressResult_81, %dataResult_82 = load[%156] %2#1 {handshake.bb = 7 : ui32, handshake.name = "load17"} : <i32>, <f32>, <i32>, <f32>
    %157 = subf %144, %152 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "subf0"} : <f32>
    %158 = mulf %157, %121 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf5"} : <f32>
    %159 = addf %dataResult_82, %158 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf4"} : <f32>
    %160 = extui %119 {handshake.bb = 7 : ui32, handshake.name = "extui18"} : <i32> to <i64>
    %161 = trunci %160 {handshake.bb = 7 : ui32, handshake.name = "index_cast18"} : <i64> to <i32>
    %addressResult_83, %dataResult_84 = store[%161] %159 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store18"} : <i32>, <f32>, <i32>, <f32>
    %162 = addi %119, %129 {handshake.bb = 7 : ui32, handshake.name = "addi4"} : <i32>
    %163 = cmpi ult, %162, %127 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_85, %falseResult_86 = cond_br %163, %162 {handshake.bb = 7 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_87, %falseResult_88 = cond_br %163, %116 {handshake.bb = 7 : ui32, handshake.name = "cond_br25"} : <i1>, <f32>
    %trueResult_89, %falseResult_90 = cond_br %163, %117 {handshake.bb = 7 : ui32, handshake.name = "cond_br26"} : <i1>, <f32>
    %trueResult_91, %falseResult_92 = cond_br %163, %118 {handshake.bb = 7 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_93, %falseResult_94 = cond_br %163, %result_65 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <>
    %trueResult_95, %falseResult_96 = cond_br %163, %130 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %164 = mux %index_98 [%falseResult_96, %trueResult_107] {handshake.bb = 8 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %165 = mux %index_98 [%falseResult_88, %trueResult_109] {handshake.bb = 8 : ui32, handshake.name = "mux22"} : <i1>, [<f32>, <f32>] to <f32>
    %166 = mux %index_98 [%falseResult_90, %trueResult_111] {handshake.bb = 8 : ui32, handshake.name = "mux23"} : <i1>, [<f32>, <f32>] to <f32>
    %167 = mux %index_98 [%falseResult_92, %trueResult_113] {handshake.bb = 8 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %result_97, %index_98 = control_merge [%falseResult_94, %trueResult_115]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %168 = source {handshake.bb = 8 : ui32, handshake.name = "source16"} : <>
    %169 = constant %168 {handshake.bb = 8 : ui32, handshake.name = "constant39", value = 1.000000e-01 : f32} : <>, <f32>
    %170 = source {handshake.bb = 8 : ui32, handshake.name = "source17"} : <>
    %171 = constant %170 {handshake.bb = 8 : ui32, handshake.name = "constant40", value = 30 : i32} : <>, <i32>
    %172 = source {handshake.bb = 8 : ui32, handshake.name = "source18"} : <>
    %173 = constant %172 {handshake.bb = 8 : ui32, handshake.name = "constant41", value = 1 : i32} : <>, <i32>
    %174 = extui %164 {handshake.bb = 8 : ui32, handshake.name = "extui19"} : <i32> to <i64>
    %175 = trunci %174 {handshake.bb = 8 : ui32, handshake.name = "index_cast19"} : <i64> to <i32>
    %addressResult_99, %dataResult_100 = load[%175] %4#1 {handshake.bb = 8 : ui32, handshake.name = "load19"} : <i32>, <f32>, <i32>, <f32>
    %176 = extui %164 {handshake.bb = 8 : ui32, handshake.name = "extui20"} : <i32> to <i64>
    %177 = trunci %176 {handshake.bb = 8 : ui32, handshake.name = "index_cast20"} : <i64> to <i32>
    %addressResult_101, %dataResult_102 = load[%177] %3#1 {handshake.bb = 8 : ui32, handshake.name = "load20"} : <i32>, <f32>, <i32>, <f32>
    %178 = mulf %dataResult_102, %169 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "mulf6"} : <f32>
    %179 = addf %dataResult_100, %178 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "addf5"} : <f32>
    %180 = extui %164 {handshake.bb = 8 : ui32, handshake.name = "extui21"} : <i32> to <i64>
    %181 = trunci %180 {handshake.bb = 8 : ui32, handshake.name = "index_cast21"} : <i64> to <i32>
    %addressResult_103, %dataResult_104 = load[%181] %2#2 {handshake.bb = 8 : ui32, handshake.name = "load21"} : <i32>, <f32>, <i32>, <f32>
    %182 = subf %179, %dataResult_104 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "subf1"} : <f32>
    %183 = extui %164 {handshake.bb = 8 : ui32, handshake.name = "extui22"} : <i32> to <i64>
    %184 = trunci %183 {handshake.bb = 8 : ui32, handshake.name = "index_cast22"} : <i64> to <i32>
    %addressResult_105, %dataResult_106 = store[%184] %182 {handshake.bb = 8 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store22"} : <i32>, <f32>, <i32>, <f32>
    %185 = addi %164, %173 {handshake.bb = 8 : ui32, handshake.name = "addi5"} : <i32>
    %186 = cmpi ult, %185, %171 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_107, %falseResult_108 = cond_br %186, %185 {handshake.bb = 8 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_109, %falseResult_110 = cond_br %186, %165 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <f32>
    %trueResult_111, %falseResult_112 = cond_br %186, %166 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <f32>
    %trueResult_113, %falseResult_114 = cond_br %186, %167 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_115, %falseResult_116 = cond_br %186, %result_97 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %187 = merge %falseResult_110 {handshake.bb = 9 : ui32, handshake.name = "merge5"} : <f32>
    %188 = merge %falseResult_112 {handshake.bb = 9 : ui32, handshake.name = "merge6"} : <f32>
    %189 = merge %falseResult_114 {handshake.bb = 9 : ui32, handshake.name = "merge7"} : <i32>
    %result_117, %index_118 = control_merge [%falseResult_116]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %190 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %191 = constant %190 {handshake.bb = 9 : ui32, handshake.name = "constant42", value = 7 : i32} : <>, <i32>
    %192 = source {handshake.bb = 9 : ui32, handshake.name = "source20"} : <>
    %193 = constant %192 {handshake.bb = 9 : ui32, handshake.name = "constant43", value = 1 : i32} : <>, <i32>
    %194 = addi %189, %193 {handshake.bb = 9 : ui32, handshake.name = "addi6"} : <i32>
    %195 = cmpi ult, %194, %191 {handshake.bb = 9 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_119, %falseResult_120 = cond_br %195, %194 {handshake.bb = 9 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_121, %falseResult_122 = cond_br %195, %187 {handshake.bb = 9 : ui32, handshake.name = "cond_br36"} : <i1>, <f32>
    %trueResult_123, %falseResult_124 = cond_br %195, %188 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <f32>
    %trueResult_125, %falseResult_126 = cond_br %195, %result_117 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %196 = constant %result_127 {handshake.bb = 10 : ui32, handshake.name = "constant1", value = 2 : i32} : <>, <i32>
    %result_127, %index_128 = control_merge [%falseResult_126]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %197 = constant %result_127 {handshake.bb = 10 : ui32, handshake.name = "constant44", value = 0 : i32} : <>, <i32>
    %198 = constant %result_127 {handshake.bb = 10 : ui32, handshake.name = "constant45", value = 1 : i32} : <>, <i32>
    %addressResult_129, %dataResult_130 = load[%197] %1#1 {handshake.bb = 10 : ui32, handshake.name = "load23"} : <i32>, <f32>, <i32>, <f32>
    %addressResult_131, %dataResult_132 = store[%197] %dataResult_130 {handshake.bb = 10 : ui32, handshake.name = "store24"} : <i32>, <f32>, <i32>, <f32>
    %addressResult_133, %dataResult_134 = load[%198] %1#2 {handshake.bb = 10 : ui32, handshake.name = "load25"} : <i32>, <f32>, <i32>, <f32>
    %addressResult_135, %dataResult_136 = store[%198] %dataResult_134 {handshake.bb = 10 : ui32, handshake.name = "store26"} : <i32>, <f32>, <i32>, <f32>
    end {handshake.bb = 10 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %4#2, %3#2, %2#3, %1#3, %0#3, %arg17 : <>, <>, <>, <>, <>, <>, <>, <>, <>
  }
}

