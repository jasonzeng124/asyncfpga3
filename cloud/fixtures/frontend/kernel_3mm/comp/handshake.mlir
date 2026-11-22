module {
  handshake.func @kernel_3mm(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: memref<100xi32>, %arg4: memref<100xi32>, %arg5: memref<100xi32>, %arg6: memref<100xi32>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, %arg13: !handshake.control<>, %arg14: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "D", "E", "F", "G", "A_start", "B_start", "C_start", "D_start", "E_start", "F_start", "G_start", "start"], resNames = ["A_end", "B_end", "C_end", "D_end", "E_end", "F_end", "G_end", "end"]} {
    %memEnd = mem_controller[%arg6 : memref<100xi32>] %arg13 (%222, %addressResult_125, %dataResult_126) %result_143 {connectedBlocks = [14 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0:2 = lsq[%arg5 : memref<100xi32>] (%arg12, %result_75, %addressResult_77, %dataResult_78, %result_101, %addressResult_105, %result_143)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:2 = lsq[%arg4 : memref<100xi32>] (%arg11, %result_27, %addressResult_29, %dataResult_30, %result_101, %addressResult_103, %result_143)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %outputs, %memEnd_0 = mem_controller[%arg3 : memref<100xi32>] %arg10 (%addressResult_57) %result_143 {connectedBlocks = [8 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg2 : memref<100xi32>] %arg9 (%addressResult_55) %result_143 {connectedBlocks = [8 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg1 : memref<100xi32>] %arg8 (%addressResult_11) %result_143 {connectedBlocks = [3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_5, %memEnd_6 = mem_controller[%arg0 : memref<100xi32>] %arg7 (%addressResult) %result_143 {connectedBlocks = [3 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %2 = constant %arg14 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <i32>
    %4 = br %arg14 {handshake.bb = 0 : ui32, handshake.name = "br8"} : <>
    %5 = mux %index [%3, %trueResult_43] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_45]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %7 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %10 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i32>
    %11 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i64>
    %12 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %13 = br %result {handshake.bb = 1 : ui32, handshake.name = "br13"} : <>
    %14 = mux %index_8 [%9, %trueResult_31] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_8 [%10, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_8 [%11, %trueResult_35] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %17 = mux %index_8 [%12, %trueResult_37] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_7, %index_8 = control_merge [%13, %trueResult_39]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %18 = constant %result_7 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %19 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %20 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i32>
    %21 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i32>
    %22 = br %16 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i64>
    %23 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <i64>
    %24 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br18"} : <i32>
    %25 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br19"} : <i64>
    %26 = br %result_7 {handshake.bb = 2 : ui32, handshake.name = "br20"} : <>
    %27 = mux %index_10 [%20, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %28 = mux %index_10 [%20, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %index_10 [%21, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %index_10 [%22, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %31 = mux %index_10 [%23, %trueResult_19] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %32 = mux %index_10 [%24, %trueResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %index_10 [%25, %trueResult_23] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i64>, <i64>] to <i64>
    %result_9, %index_10 = control_merge [%26, %trueResult_25]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 10 : i32} : <>, <i32>
    %36 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %37 = constant %36 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %38 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %39 = constant %38 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 3 : i64} : <>, <i64>
    %40 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %41 = constant %40 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i64} : <>, <i64>
    %42 = extui %28 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %43 = shli %30, %41 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %44 = shli %30, %39 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %45 = addi %43, %44 {handshake.bb = 3 : ui32, handshake.name = "addi21"} : <i64>
    %46 = addi %45, %42 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i64>
    %47 = trunci %46 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%47] %outputs_5 {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %48 = extui %28 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %49 = shli %48, %41 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %50 = shli %48, %39 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %51 = addi %49, %50 {handshake.bb = 3 : ui32, handshake.name = "addi22"} : <i64>
    %52 = addi %51, %33 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i64>
    %53 = trunci %52 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_11, %dataResult_12 = load[%53] %outputs_3 {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %54 = muli %dataResult, %dataResult_12 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %55 = addi %27, %54 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %56 = addi %28, %37 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %57 = cmpi ult, %56, %35 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %57, %55 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %57, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %57, %29 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_17, %falseResult_18 = cond_br %57, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i64>
    %trueResult_19, %falseResult_20 = cond_br %57, %31 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_21, %falseResult_22 = cond_br %57, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_23, %falseResult_24 = cond_br %57, %33 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i64>
    %trueResult_25, %falseResult_26 = cond_br %57, %result_9 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %58 = merge %falseResult {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %59 = merge %falseResult_16 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %60 = merge %falseResult_18 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i64>
    %61 = merge %falseResult_20 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i64>
    %62 = merge %falseResult_22 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i32>
    %result_27, %index_28 = control_merge [%falseResult_26]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %63 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %64 = constant %63 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 10 : i32} : <>, <i32>
    %65 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %66 = constant %65 {handshake.bb = 4 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %67 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %68 = constant %67 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %69 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %70 = constant %69 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1 : i64} : <>, <i64>
    %71 = extui %62 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %72 = shli %61, %70 {handshake.bb = 4 : ui32, handshake.name = "shli4"} : <i64>
    %73 = shli %61, %68 {handshake.bb = 4 : ui32, handshake.name = "shli5"} : <i64>
    %74 = addi %72, %73 {handshake.bb = 4 : ui32, handshake.name = "addi23"} : <i64>
    %75 = addi %74, %71 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i64>
    %76 = trunci %75 {handshake.bb = 4 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_29, %dataResult_30 = store[%76] %58 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %77 = addi %62, %66 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %78 = cmpi ult, %77, %64 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_31, %falseResult_32 = cond_br %78, %77 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_33, %falseResult_34 = cond_br %78, %59 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_35, %falseResult_36 = cond_br %78, %60 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i64>
    %trueResult_37, %falseResult_38 = cond_br %78, %61 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i64>
    %trueResult_39, %falseResult_40 = cond_br %78, %result_27 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <>
    %79 = merge %falseResult_34 {handshake.bb = 5 : ui32, handshake.name = "merge5"} : <i32>
    %result_41, %index_42 = control_merge [%falseResult_40]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %80 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %81 = constant %80 {handshake.bb = 5 : ui32, handshake.name = "constant16", value = 10 : i32} : <>, <i32>
    %82 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %83 = constant %82 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %84 = constant %result_41 {handshake.bb = 5 : ui32, handshake.name = "constant18", value = 0 : i32} : <>, <i32>
    %85 = addi %79, %83 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %86 = cmpi ult, %85, %81 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_43, %falseResult_44 = cond_br %86, %85 {handshake.bb = 5 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_45, %falseResult_46 = cond_br %86, %result_41 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %trueResult_47, %falseResult_48 = cond_br %86, %84 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %87 = mux %index_50 [%falseResult_48, %trueResult_91] {handshake.bb = 6 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_49, %index_50 = control_merge [%falseResult_46, %trueResult_93]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %88 = constant %result_49 {handshake.bb = 6 : ui32, handshake.name = "constant19", value = 0 : i32} : <>, <i32>
    %89 = extui %87 {handshake.bb = 6 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %90 = extui %87 {handshake.bb = 6 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %91 = br %88 {handshake.bb = 6 : ui32, handshake.name = "br21"} : <i32>
    %92 = br %87 {handshake.bb = 6 : ui32, handshake.name = "br22"} : <i32>
    %93 = br %89 {handshake.bb = 6 : ui32, handshake.name = "br23"} : <i64>
    %94 = br %90 {handshake.bb = 6 : ui32, handshake.name = "br24"} : <i64>
    %95 = br %result_49 {handshake.bb = 6 : ui32, handshake.name = "br25"} : <>
    %96 = mux %index_52 [%91, %trueResult_79] {handshake.bb = 7 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %97 = mux %index_52 [%92, %trueResult_81] {handshake.bb = 7 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %98 = mux %index_52 [%93, %trueResult_83] {handshake.bb = 7 : ui32, handshake.name = "mux15"} : <i1>, [<i64>, <i64>] to <i64>
    %99 = mux %index_52 [%94, %trueResult_85] {handshake.bb = 7 : ui32, handshake.name = "mux16"} : <i1>, [<i64>, <i64>] to <i64>
    %result_51, %index_52 = control_merge [%95, %trueResult_87]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %100 = constant %result_51 {handshake.bb = 7 : ui32, handshake.name = "constant20", value = 0 : i32} : <>, <i32>
    %101 = extui %96 {handshake.bb = 7 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %102 = br %100 {handshake.bb = 7 : ui32, handshake.name = "br26"} : <i32>
    %103 = br %97 {handshake.bb = 7 : ui32, handshake.name = "br27"} : <i32>
    %104 = br %98 {handshake.bb = 7 : ui32, handshake.name = "br28"} : <i64>
    %105 = br %99 {handshake.bb = 7 : ui32, handshake.name = "br29"} : <i64>
    %106 = br %96 {handshake.bb = 7 : ui32, handshake.name = "br30"} : <i32>
    %107 = br %101 {handshake.bb = 7 : ui32, handshake.name = "br31"} : <i64>
    %108 = br %result_51 {handshake.bb = 7 : ui32, handshake.name = "br32"} : <>
    %109 = mux %index_54 [%102, %trueResult_59] {handshake.bb = 8 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %110 = mux %index_54 [%102, %trueResult_61] {handshake.bb = 8 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %111 = mux %index_54 [%103, %trueResult_63] {handshake.bb = 8 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %112 = mux %index_54 [%104, %trueResult_65] {handshake.bb = 8 : ui32, handshake.name = "mux20"} : <i1>, [<i64>, <i64>] to <i64>
    %113 = mux %index_54 [%105, %trueResult_67] {handshake.bb = 8 : ui32, handshake.name = "mux21"} : <i1>, [<i64>, <i64>] to <i64>
    %114 = mux %index_54 [%106, %trueResult_69] {handshake.bb = 8 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %115 = mux %index_54 [%107, %trueResult_71] {handshake.bb = 8 : ui32, handshake.name = "mux23"} : <i1>, [<i64>, <i64>] to <i64>
    %result_53, %index_54 = control_merge [%108, %trueResult_73]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %116 = source {handshake.bb = 8 : ui32, handshake.name = "source10"} : <>
    %117 = constant %116 {handshake.bb = 8 : ui32, handshake.name = "constant21", value = 10 : i32} : <>, <i32>
    %118 = source {handshake.bb = 8 : ui32, handshake.name = "source11"} : <>
    %119 = constant %118 {handshake.bb = 8 : ui32, handshake.name = "constant22", value = 1 : i32} : <>, <i32>
    %120 = source {handshake.bb = 8 : ui32, handshake.name = "source12"} : <>
    %121 = constant %120 {handshake.bb = 8 : ui32, handshake.name = "constant23", value = 3 : i64} : <>, <i64>
    %122 = source {handshake.bb = 8 : ui32, handshake.name = "source13"} : <>
    %123 = constant %122 {handshake.bb = 8 : ui32, handshake.name = "constant24", value = 1 : i64} : <>, <i64>
    %124 = extui %109 {handshake.bb = 8 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %125 = shli %112, %123 {handshake.bb = 8 : ui32, handshake.name = "shli6"} : <i64>
    %126 = shli %112, %121 {handshake.bb = 8 : ui32, handshake.name = "shli7"} : <i64>
    %127 = addi %125, %126 {handshake.bb = 8 : ui32, handshake.name = "addi24"} : <i64>
    %128 = addi %127, %124 {handshake.bb = 8 : ui32, handshake.name = "addi7"} : <i64>
    %129 = trunci %128 {handshake.bb = 8 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_55, %dataResult_56 = load[%129] %outputs_1 {handshake.bb = 8 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %130 = extui %109 {handshake.bb = 8 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %131 = shli %130, %123 {handshake.bb = 8 : ui32, handshake.name = "shli8"} : <i64>
    %132 = shli %130, %121 {handshake.bb = 8 : ui32, handshake.name = "shli9"} : <i64>
    %133 = addi %131, %132 {handshake.bb = 8 : ui32, handshake.name = "addi25"} : <i64>
    %134 = addi %133, %115 {handshake.bb = 8 : ui32, handshake.name = "addi8"} : <i64>
    %135 = trunci %134 {handshake.bb = 8 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_57, %dataResult_58 = load[%135] %outputs {handshake.bb = 8 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %136 = muli %dataResult_56, %dataResult_58 {handshake.bb = 8 : ui32, handshake.name = "muli6"} : <i32>
    %137 = addi %110, %136 {handshake.bb = 8 : ui32, handshake.name = "addi9"} : <i32>
    %138 = addi %109, %119 {handshake.bb = 8 : ui32, handshake.name = "addi10"} : <i32>
    %139 = cmpi ult, %138, %117 {handshake.bb = 8 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_59, %falseResult_60 = cond_br %139, %138 {handshake.bb = 8 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_61, %falseResult_62 = cond_br %139, %137 {handshake.bb = 8 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_63, %falseResult_64 = cond_br %139, %111 {handshake.bb = 8 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_65, %falseResult_66 = cond_br %139, %112 {handshake.bb = 8 : ui32, handshake.name = "cond_br28"} : <i1>, <i64>
    %trueResult_67, %falseResult_68 = cond_br %139, %113 {handshake.bb = 8 : ui32, handshake.name = "cond_br29"} : <i1>, <i64>
    %trueResult_69, %falseResult_70 = cond_br %139, %114 {handshake.bb = 8 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_71, %falseResult_72 = cond_br %139, %115 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <i64>
    %trueResult_73, %falseResult_74 = cond_br %139, %result_53 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <>
    %140 = merge %falseResult_62 {handshake.bb = 9 : ui32, handshake.name = "merge6"} : <i32>
    %141 = merge %falseResult_64 {handshake.bb = 9 : ui32, handshake.name = "merge7"} : <i32>
    %142 = merge %falseResult_66 {handshake.bb = 9 : ui32, handshake.name = "merge8"} : <i64>
    %143 = merge %falseResult_68 {handshake.bb = 9 : ui32, handshake.name = "merge9"} : <i64>
    %144 = merge %falseResult_70 {handshake.bb = 9 : ui32, handshake.name = "merge10"} : <i32>
    %result_75, %index_76 = control_merge [%falseResult_74]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %145 = source {handshake.bb = 9 : ui32, handshake.name = "source14"} : <>
    %146 = constant %145 {handshake.bb = 9 : ui32, handshake.name = "constant25", value = 10 : i32} : <>, <i32>
    %147 = source {handshake.bb = 9 : ui32, handshake.name = "source15"} : <>
    %148 = constant %147 {handshake.bb = 9 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %149 = source {handshake.bb = 9 : ui32, handshake.name = "source16"} : <>
    %150 = constant %149 {handshake.bb = 9 : ui32, handshake.name = "constant27", value = 3 : i64} : <>, <i64>
    %151 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %152 = constant %151 {handshake.bb = 9 : ui32, handshake.name = "constant28", value = 1 : i64} : <>, <i64>
    %153 = extui %144 {handshake.bb = 9 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %154 = shli %143, %152 {handshake.bb = 9 : ui32, handshake.name = "shli10"} : <i64>
    %155 = shli %143, %150 {handshake.bb = 9 : ui32, handshake.name = "shli11"} : <i64>
    %156 = addi %154, %155 {handshake.bb = 9 : ui32, handshake.name = "addi26"} : <i64>
    %157 = addi %156, %153 {handshake.bb = 9 : ui32, handshake.name = "addi11"} : <i64>
    %158 = trunci %157 {handshake.bb = 9 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_77, %dataResult_78 = store[%158] %140 {handshake.bb = 9 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %159 = addi %144, %148 {handshake.bb = 9 : ui32, handshake.name = "addi12"} : <i32>
    %160 = cmpi ult, %159, %146 {handshake.bb = 9 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_79, %falseResult_80 = cond_br %160, %159 {handshake.bb = 9 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_81, %falseResult_82 = cond_br %160, %141 {handshake.bb = 9 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_83, %falseResult_84 = cond_br %160, %142 {handshake.bb = 9 : ui32, handshake.name = "cond_br35"} : <i1>, <i64>
    %trueResult_85, %falseResult_86 = cond_br %160, %143 {handshake.bb = 9 : ui32, handshake.name = "cond_br36"} : <i1>, <i64>
    %trueResult_87, %falseResult_88 = cond_br %160, %result_75 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <>
    %161 = merge %falseResult_82 {handshake.bb = 10 : ui32, handshake.name = "merge11"} : <i32>
    %result_89, %index_90 = control_merge [%falseResult_88]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %162 = source {handshake.bb = 10 : ui32, handshake.name = "source18"} : <>
    %163 = constant %162 {handshake.bb = 10 : ui32, handshake.name = "constant29", value = 10 : i32} : <>, <i32>
    %164 = source {handshake.bb = 10 : ui32, handshake.name = "source19"} : <>
    %165 = constant %164 {handshake.bb = 10 : ui32, handshake.name = "constant30", value = 1 : i32} : <>, <i32>
    %166 = constant %result_89 {handshake.bb = 10 : ui32, handshake.name = "constant31", value = 0 : i32} : <>, <i32>
    %167 = addi %161, %165 {handshake.bb = 10 : ui32, handshake.name = "addi13"} : <i32>
    %168 = cmpi ult, %167, %163 {handshake.bb = 10 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_91, %falseResult_92 = cond_br %168, %167 {handshake.bb = 10 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_93, %falseResult_94 = cond_br %168, %result_89 {handshake.bb = 10 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %trueResult_95, %falseResult_96 = cond_br %168, %166 {handshake.bb = 10 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %169 = mux %index_98 [%falseResult_96, %trueResult_139] {handshake.bb = 11 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %result_97, %index_98 = control_merge [%falseResult_94, %trueResult_141]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>, <>] to <>, <i1>
    %170 = constant %result_97 {handshake.bb = 11 : ui32, handshake.name = "constant32", value = 0 : i32} : <>, <i32>
    %171 = extui %169 {handshake.bb = 11 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %172 = extui %169 {handshake.bb = 11 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %173 = br %170 {handshake.bb = 11 : ui32, handshake.name = "br33"} : <i32>
    %174 = br %169 {handshake.bb = 11 : ui32, handshake.name = "br34"} : <i32>
    %175 = br %171 {handshake.bb = 11 : ui32, handshake.name = "br35"} : <i64>
    %176 = br %172 {handshake.bb = 11 : ui32, handshake.name = "br36"} : <i64>
    %177 = br %result_97 {handshake.bb = 11 : ui32, handshake.name = "br37"} : <>
    %178 = mux %index_100 [%173, %trueResult_127] {handshake.bb = 12 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %179 = mux %index_100 [%174, %trueResult_129] {handshake.bb = 12 : ui32, handshake.name = "mux26"} : <i1>, [<i32>, <i32>] to <i32>
    %180 = mux %index_100 [%175, %trueResult_131] {handshake.bb = 12 : ui32, handshake.name = "mux27"} : <i1>, [<i64>, <i64>] to <i64>
    %181 = mux %index_100 [%176, %trueResult_133] {handshake.bb = 12 : ui32, handshake.name = "mux28"} : <i1>, [<i64>, <i64>] to <i64>
    %result_99, %index_100 = control_merge [%177, %trueResult_135]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>, <>] to <>, <i1>
    %182 = constant %result_99 {handshake.bb = 12 : ui32, handshake.name = "constant33", value = 0 : i32} : <>, <i32>
    %183 = extui %178 {handshake.bb = 12 : ui32, handshake.name = "extui14"} : <i32> to <i64>
    %184 = br %182 {handshake.bb = 12 : ui32, handshake.name = "br38"} : <i32>
    %185 = br %179 {handshake.bb = 12 : ui32, handshake.name = "br39"} : <i32>
    %186 = br %180 {handshake.bb = 12 : ui32, handshake.name = "br40"} : <i64>
    %187 = br %181 {handshake.bb = 12 : ui32, handshake.name = "br41"} : <i64>
    %188 = br %178 {handshake.bb = 12 : ui32, handshake.name = "br42"} : <i32>
    %189 = br %183 {handshake.bb = 12 : ui32, handshake.name = "br43"} : <i64>
    %190 = br %result_99 {handshake.bb = 12 : ui32, handshake.name = "br44"} : <>
    %191 = mux %index_102 [%184, %trueResult_107] {handshake.bb = 13 : ui32, handshake.name = "mux29"} : <i1>, [<i32>, <i32>] to <i32>
    %192 = mux %index_102 [%184, %trueResult_109] {handshake.bb = 13 : ui32, handshake.name = "mux30"} : <i1>, [<i32>, <i32>] to <i32>
    %193 = mux %index_102 [%185, %trueResult_111] {handshake.bb = 13 : ui32, handshake.name = "mux31"} : <i1>, [<i32>, <i32>] to <i32>
    %194 = mux %index_102 [%186, %trueResult_113] {handshake.bb = 13 : ui32, handshake.name = "mux32"} : <i1>, [<i64>, <i64>] to <i64>
    %195 = mux %index_102 [%187, %trueResult_115] {handshake.bb = 13 : ui32, handshake.name = "mux33"} : <i1>, [<i64>, <i64>] to <i64>
    %196 = mux %index_102 [%188, %trueResult_117] {handshake.bb = 13 : ui32, handshake.name = "mux34"} : <i1>, [<i32>, <i32>] to <i32>
    %197 = mux %index_102 [%189, %trueResult_119] {handshake.bb = 13 : ui32, handshake.name = "mux35"} : <i1>, [<i64>, <i64>] to <i64>
    %result_101, %index_102 = control_merge [%190, %trueResult_121]  {handshake.bb = 13 : ui32, handshake.name = "control_merge12"} : [<>, <>] to <>, <i1>
    %198 = source {handshake.bb = 13 : ui32, handshake.name = "source20"} : <>
    %199 = constant %198 {handshake.bb = 13 : ui32, handshake.name = "constant34", value = 10 : i32} : <>, <i32>
    %200 = source {handshake.bb = 13 : ui32, handshake.name = "source21"} : <>
    %201 = constant %200 {handshake.bb = 13 : ui32, handshake.name = "constant35", value = 1 : i32} : <>, <i32>
    %202 = source {handshake.bb = 13 : ui32, handshake.name = "source22"} : <>
    %203 = constant %202 {handshake.bb = 13 : ui32, handshake.name = "constant36", value = 3 : i64} : <>, <i64>
    %204 = source {handshake.bb = 13 : ui32, handshake.name = "source23"} : <>
    %205 = constant %204 {handshake.bb = 13 : ui32, handshake.name = "constant37", value = 1 : i64} : <>, <i64>
    %206 = extui %191 {handshake.bb = 13 : ui32, handshake.name = "extui15"} : <i32> to <i64>
    %207 = shli %194, %205 {handshake.bb = 13 : ui32, handshake.name = "shli12"} : <i64>
    %208 = shli %194, %203 {handshake.bb = 13 : ui32, handshake.name = "shli13"} : <i64>
    %209 = addi %207, %208 {handshake.bb = 13 : ui32, handshake.name = "addi27"} : <i64>
    %210 = addi %209, %206 {handshake.bb = 13 : ui32, handshake.name = "addi14"} : <i64>
    %211 = trunci %210 {handshake.bb = 13 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_103, %dataResult_104 = load[%211] %1#0 {handshake.bb = 13 : ui32, handshake.name = "load6"} : <i32>, <i32>, <i32>, <i32>
    %212 = extui %191 {handshake.bb = 13 : ui32, handshake.name = "extui16"} : <i32> to <i64>
    %213 = shli %212, %205 {handshake.bb = 13 : ui32, handshake.name = "shli14"} : <i64>
    %214 = shli %212, %203 {handshake.bb = 13 : ui32, handshake.name = "shli15"} : <i64>
    %215 = addi %213, %214 {handshake.bb = 13 : ui32, handshake.name = "addi28"} : <i64>
    %216 = addi %215, %197 {handshake.bb = 13 : ui32, handshake.name = "addi15"} : <i64>
    %217 = trunci %216 {handshake.bb = 13 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_105, %dataResult_106 = load[%217] %0#0 {handshake.bb = 13 : ui32, handshake.name = "load7"} : <i32>, <i32>, <i32>, <i32>
    %218 = muli %dataResult_104, %dataResult_106 {handshake.bb = 13 : ui32, handshake.name = "muli10"} : <i32>
    %219 = addi %192, %218 {handshake.bb = 13 : ui32, handshake.name = "addi16"} : <i32>
    %220 = addi %191, %201 {handshake.bb = 13 : ui32, handshake.name = "addi17"} : <i32>
    %221 = cmpi ult, %220, %199 {handshake.bb = 13 : ui32, handshake.name = "cmpi6"} : <i32>
    %trueResult_107, %falseResult_108 = cond_br %221, %220 {handshake.bb = 13 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    %trueResult_109, %falseResult_110 = cond_br %221, %219 {handshake.bb = 13 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_111, %falseResult_112 = cond_br %221, %193 {handshake.bb = 13 : ui32, handshake.name = "cond_br43"} : <i1>, <i32>
    %trueResult_113, %falseResult_114 = cond_br %221, %194 {handshake.bb = 13 : ui32, handshake.name = "cond_br44"} : <i1>, <i64>
    %trueResult_115, %falseResult_116 = cond_br %221, %195 {handshake.bb = 13 : ui32, handshake.name = "cond_br45"} : <i1>, <i64>
    %trueResult_117, %falseResult_118 = cond_br %221, %196 {handshake.bb = 13 : ui32, handshake.name = "cond_br46"} : <i1>, <i32>
    %trueResult_119, %falseResult_120 = cond_br %221, %197 {handshake.bb = 13 : ui32, handshake.name = "cond_br47"} : <i1>, <i64>
    %trueResult_121, %falseResult_122 = cond_br %221, %result_101 {handshake.bb = 13 : ui32, handshake.name = "cond_br48"} : <i1>, <>
    %222 = constant %result_123 {handshake.bb = 14 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %223 = merge %falseResult_110 {handshake.bb = 14 : ui32, handshake.name = "merge12"} : <i32>
    %224 = merge %falseResult_112 {handshake.bb = 14 : ui32, handshake.name = "merge13"} : <i32>
    %225 = merge %falseResult_114 {handshake.bb = 14 : ui32, handshake.name = "merge14"} : <i64>
    %226 = merge %falseResult_116 {handshake.bb = 14 : ui32, handshake.name = "merge15"} : <i64>
    %227 = merge %falseResult_118 {handshake.bb = 14 : ui32, handshake.name = "merge16"} : <i32>
    %result_123, %index_124 = control_merge [%falseResult_122]  {handshake.bb = 14 : ui32, handshake.name = "control_merge13"} : [<>] to <>, <i1>
    %228 = source {handshake.bb = 14 : ui32, handshake.name = "source24"} : <>
    %229 = constant %228 {handshake.bb = 14 : ui32, handshake.name = "constant38", value = 10 : i32} : <>, <i32>
    %230 = source {handshake.bb = 14 : ui32, handshake.name = "source25"} : <>
    %231 = constant %230 {handshake.bb = 14 : ui32, handshake.name = "constant39", value = 1 : i32} : <>, <i32>
    %232 = source {handshake.bb = 14 : ui32, handshake.name = "source26"} : <>
    %233 = constant %232 {handshake.bb = 14 : ui32, handshake.name = "constant40", value = 3 : i64} : <>, <i64>
    %234 = source {handshake.bb = 14 : ui32, handshake.name = "source27"} : <>
    %235 = constant %234 {handshake.bb = 14 : ui32, handshake.name = "constant41", value = 1 : i64} : <>, <i64>
    %236 = extui %227 {handshake.bb = 14 : ui32, handshake.name = "extui17"} : <i32> to <i64>
    %237 = shli %226, %235 {handshake.bb = 14 : ui32, handshake.name = "shli16"} : <i64>
    %238 = shli %226, %233 {handshake.bb = 14 : ui32, handshake.name = "shli17"} : <i64>
    %239 = addi %237, %238 {handshake.bb = 14 : ui32, handshake.name = "addi29"} : <i64>
    %240 = addi %239, %236 {handshake.bb = 14 : ui32, handshake.name = "addi18"} : <i64>
    %241 = trunci %240 {handshake.bb = 14 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_125, %dataResult_126 = store[%241] %223 {handshake.bb = 14 : ui32, handshake.name = "store8"} : <i32>, <i32>, <i32>, <i32>
    %242 = addi %227, %231 {handshake.bb = 14 : ui32, handshake.name = "addi19"} : <i32>
    %243 = cmpi ult, %242, %229 {handshake.bb = 14 : ui32, handshake.name = "cmpi7"} : <i32>
    %trueResult_127, %falseResult_128 = cond_br %243, %242 {handshake.bb = 14 : ui32, handshake.name = "cond_br49"} : <i1>, <i32>
    %trueResult_129, %falseResult_130 = cond_br %243, %224 {handshake.bb = 14 : ui32, handshake.name = "cond_br50"} : <i1>, <i32>
    %trueResult_131, %falseResult_132 = cond_br %243, %225 {handshake.bb = 14 : ui32, handshake.name = "cond_br51"} : <i1>, <i64>
    %trueResult_133, %falseResult_134 = cond_br %243, %226 {handshake.bb = 14 : ui32, handshake.name = "cond_br52"} : <i1>, <i64>
    %trueResult_135, %falseResult_136 = cond_br %243, %result_123 {handshake.bb = 14 : ui32, handshake.name = "cond_br53"} : <i1>, <>
    %244 = merge %falseResult_130 {handshake.bb = 15 : ui32, handshake.name = "merge17"} : <i32>
    %result_137, %index_138 = control_merge [%falseResult_136]  {handshake.bb = 15 : ui32, handshake.name = "control_merge14"} : [<>] to <>, <i1>
    %245 = source {handshake.bb = 15 : ui32, handshake.name = "source28"} : <>
    %246 = constant %245 {handshake.bb = 15 : ui32, handshake.name = "constant42", value = 10 : i32} : <>, <i32>
    %247 = source {handshake.bb = 15 : ui32, handshake.name = "source29"} : <>
    %248 = constant %247 {handshake.bb = 15 : ui32, handshake.name = "constant43", value = 1 : i32} : <>, <i32>
    %249 = addi %244, %248 {handshake.bb = 15 : ui32, handshake.name = "addi20"} : <i32>
    %250 = cmpi ult, %249, %246 {handshake.bb = 15 : ui32, handshake.name = "cmpi8"} : <i32>
    %trueResult_139, %falseResult_140 = cond_br %250, %249 {handshake.bb = 15 : ui32, handshake.name = "cond_br54"} : <i1>, <i32>
    %trueResult_141, %falseResult_142 = cond_br %250, %result_137 {handshake.bb = 15 : ui32, handshake.name = "cond_br55"} : <i1>, <>
    %result_143, %index_144 = control_merge [%falseResult_142]  {handshake.bb = 16 : ui32, handshake.name = "control_merge15"} : [<>] to <>, <i1>
    end {handshake.bb = 16 : ui32, handshake.name = "end0"} %memEnd_6, %memEnd_4, %memEnd_2, %memEnd_0, %1#1, %0#1, %memEnd, %arg14 : <>, <>, <>, <>, <>, <>, <>, <>
  }
}

