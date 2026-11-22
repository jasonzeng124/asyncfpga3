module {
  handshake.func @covariance(%arg0: memref<900xi32>, %arg1: memref<900xi32>, %arg2: memref<30xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["data", "symmat", "mean", "data_start", "symmat_start", "mean_start", "start"], resNames = ["data_end", "symmat_end", "mean_end", "end"]} {
    %0:2 = lsq[%arg2 : memref<30xi32>] (%arg5, %result_10, %addressResult_12, %dataResult_13, %result_22, %addressResult_24, %result_88)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = lsq[%arg1 : memref<900xi32>] (%arg4, %result_70, %addressResult_72, %dataResult_73, %addressResult_74, %dataResult_75, %result_88)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> !handshake.control<>
    %outputs:2, %memEnd = mem_controller[%arg0 : memref<900xi32>] %arg3 (%61, %addressResult_26, %2#3, %2#4, %2#5) %result_88 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %2:6 = lsq[MC] (%result_0, %addressResult, %result_22, %addressResult_28, %dataResult_29, %result_50, %addressResult_52, %addressResult_54, %outputs#1)  {groupSizes = [1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %3 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %5 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %6 = mux %index [%4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %8 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %9 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %11 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i64>
    %12 = br %result {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %13 = mux %index_1 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_1 [%9, %trueResult_2] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_1 [%10, %trueResult_4] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_1 [%11, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_0, %index_1 = control_merge [%12, %trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 30 : i32} : <>, <i32>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %29 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %30 = shli %29, %28 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %31 = shli %29, %26 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %32 = addi %30, %31 {handshake.bb = 2 : ui32, handshake.name = "addi15"} : <i64>
    %33 = shli %29, %24 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %34 = shli %29, %22 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %35 = addi %33, %34 {handshake.bb = 2 : ui32, handshake.name = "addi16"} : <i64>
    %36 = addi %32, %35 {handshake.bb = 2 : ui32, handshake.name = "addi17"} : <i64>
    %37 = addi %36, %16 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %38 = trunci %37 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%38] %2#0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %39 = addi %13, %dataResult {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %40 = addi %14, %20 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %41 = cmpi ult, %40, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %41, %39 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %41, %40 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %41, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %41, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i64>
    %trueResult_8, %falseResult_9 = cond_br %41, %result_0 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %42 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %43 = merge %falseResult_5 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_9]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 30 : i32} : <>, <i32>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %47 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %48 = constant %result_10 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 0 : i32} : <>, <i32>
    %49 = divsi %42, %45 {handshake.bb = 3 : ui32, handshake.name = "divsi0"} : <i32>
    %50 = extui %43 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %51 = trunci %50 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%51] %49 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %52 = addi %43, %47 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %53 = cmpi ult, %52, %45 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %53, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %53, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_18, %falseResult_19 = cond_br %53, %48 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %54 = mux %index_21 [%falseResult_19, %trueResult_40] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_17, %trueResult_42]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %55 = constant %result_20 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 0 : i32} : <>, <i32>
    %56 = extui %54 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %57 = br %55 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <i32>
    %58 = br %54 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i32>
    %59 = br %56 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <i64>
    %60 = br %result_20 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <>
    %61 = constant %result_22 {handshake.bb = 5 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %62 = mux %index_23 [%57, %trueResult_30] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %63 = mux %index_23 [%58, %trueResult_32] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %64 = mux %index_23 [%59, %trueResult_34] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %result_22, %index_23 = control_merge [%60, %trueResult_36]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %65 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %66 = constant %65 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 30 : i32} : <>, <i32>
    %67 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %68 = constant %67 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %69 = source {handshake.bb = 5 : ui32, handshake.name = "source10"} : <>
    %70 = constant %69 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = 4 : i64} : <>, <i64>
    %71 = source {handshake.bb = 5 : ui32, handshake.name = "source11"} : <>
    %72 = constant %71 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 3 : i64} : <>, <i64>
    %73 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %74 = constant %73 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 2 : i64} : <>, <i64>
    %75 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %76 = constant %75 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i64} : <>, <i64>
    %77 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %78 = trunci %77 {handshake.bb = 5 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = load[%78] %0#0 {handshake.bb = 5 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %79 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %80 = shli %64, %76 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %81 = shli %64, %74 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %82 = addi %80, %81 {handshake.bb = 5 : ui32, handshake.name = "addi18"} : <i64>
    %83 = shli %64, %72 {handshake.bb = 5 : ui32, handshake.name = "shli6"} : <i64>
    %84 = shli %64, %70 {handshake.bb = 5 : ui32, handshake.name = "shli7"} : <i64>
    %85 = addi %83, %84 {handshake.bb = 5 : ui32, handshake.name = "addi19"} : <i64>
    %86 = addi %82, %85 {handshake.bb = 5 : ui32, handshake.name = "addi20"} : <i64>
    %87 = addi %86, %79 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i64>
    %88 = trunci %87 {handshake.bb = 5 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_26, %dataResult_27 = load[%88] %outputs#0 {handshake.bb = 5 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %89 = subi %dataResult_27, %dataResult_25 {handshake.bb = 5 : ui32, handshake.name = "subi0"} : <i32>
    %90 = trunci %87 {handshake.bb = 5 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_28, %dataResult_29 = store[%90] %89 {handshake.bb = 5 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %91 = addi %62, %68 {handshake.bb = 5 : ui32, handshake.name = "addi5"} : <i32>
    %92 = cmpi ult, %91, %66 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_30, %falseResult_31 = cond_br %92, %91 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %92, %63 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %92, %64 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i64>
    %trueResult_36, %falseResult_37 = cond_br %92, %result_22 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %93 = merge %falseResult_33 {handshake.bb = 6 : ui32, handshake.name = "merge2"} : <i32>
    %result_38, %index_39 = control_merge [%falseResult_37]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %94 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %95 = constant %94 {handshake.bb = 6 : ui32, handshake.name = "constant25", value = 30 : i32} : <>, <i32>
    %96 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %97 = constant %96 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %98 = constant %result_38 {handshake.bb = 6 : ui32, handshake.name = "constant27", value = 0 : i32} : <>, <i32>
    %99 = addi %93, %97 {handshake.bb = 6 : ui32, handshake.name = "addi6"} : <i32>
    %100 = cmpi ult, %99, %95 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %100, %99 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %100, %result_38 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %trueResult_44, %falseResult_45 = cond_br %100, %98 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %101 = mux %index_47 [%falseResult_45, %trueResult_84] {handshake.bb = 7 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%falseResult_43, %trueResult_86]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %102 = br %101 {handshake.bb = 7 : ui32, handshake.name = "br15"} : <i32>
    %103 = br %result_46 {handshake.bb = 7 : ui32, handshake.name = "br16"} : <>
    %104 = mux %index_49 [%102, %trueResult_76] {handshake.bb = 8 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %105 = mux %index_49 [%102, %trueResult_78] {handshake.bb = 8 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_48, %index_49 = control_merge [%103, %trueResult_80]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %106 = constant %result_48 {handshake.bb = 8 : ui32, handshake.name = "constant28", value = 0 : i32} : <>, <i32>
    %107 = extui %105 {handshake.bb = 8 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %108 = extui %104 {handshake.bb = 8 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %109 = br %106 {handshake.bb = 8 : ui32, handshake.name = "br17"} : <i32>
    %110 = br %105 {handshake.bb = 8 : ui32, handshake.name = "br18"} : <i32>
    %111 = br %104 {handshake.bb = 8 : ui32, handshake.name = "br19"} : <i32>
    %112 = br %107 {handshake.bb = 8 : ui32, handshake.name = "br20"} : <i64>
    %113 = br %108 {handshake.bb = 8 : ui32, handshake.name = "br21"} : <i64>
    %114 = br %result_48 {handshake.bb = 8 : ui32, handshake.name = "br22"} : <>
    %115 = mux %index_51 [%109, %trueResult_56] {handshake.bb = 9 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %116 = mux %index_51 [%109, %trueResult_58] {handshake.bb = 9 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %117 = mux %index_51 [%110, %trueResult_60] {handshake.bb = 9 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %118 = mux %index_51 [%111, %trueResult_62] {handshake.bb = 9 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %119 = mux %index_51 [%112, %trueResult_64] {handshake.bb = 9 : ui32, handshake.name = "mux16"} : <i1>, [<i64>, <i64>] to <i64>
    %120 = mux %index_51 [%113, %trueResult_66] {handshake.bb = 9 : ui32, handshake.name = "mux17"} : <i1>, [<i64>, <i64>] to <i64>
    %result_50, %index_51 = control_merge [%114, %trueResult_68]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>, <>] to <>, <i1>
    %121 = source {handshake.bb = 9 : ui32, handshake.name = "source16"} : <>
    %122 = constant %121 {handshake.bb = 9 : ui32, handshake.name = "constant29", value = 30 : i32} : <>, <i32>
    %123 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %124 = constant %123 {handshake.bb = 9 : ui32, handshake.name = "constant30", value = 1 : i32} : <>, <i32>
    %125 = source {handshake.bb = 9 : ui32, handshake.name = "source18"} : <>
    %126 = constant %125 {handshake.bb = 9 : ui32, handshake.name = "constant31", value = 4 : i64} : <>, <i64>
    %127 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %128 = constant %127 {handshake.bb = 9 : ui32, handshake.name = "constant32", value = 3 : i64} : <>, <i64>
    %129 = source {handshake.bb = 9 : ui32, handshake.name = "source20"} : <>
    %130 = constant %129 {handshake.bb = 9 : ui32, handshake.name = "constant33", value = 2 : i64} : <>, <i64>
    %131 = source {handshake.bb = 9 : ui32, handshake.name = "source21"} : <>
    %132 = constant %131 {handshake.bb = 9 : ui32, handshake.name = "constant34", value = 1 : i64} : <>, <i64>
    %133 = extui %116 {handshake.bb = 9 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %134 = shli %133, %132 {handshake.bb = 9 : ui32, handshake.name = "shli8"} : <i64>
    %135 = shli %133, %130 {handshake.bb = 9 : ui32, handshake.name = "shli9"} : <i64>
    %136 = addi %134, %135 {handshake.bb = 9 : ui32, handshake.name = "addi21"} : <i64>
    %137 = shli %133, %128 {handshake.bb = 9 : ui32, handshake.name = "shli10"} : <i64>
    %138 = shli %133, %126 {handshake.bb = 9 : ui32, handshake.name = "shli11"} : <i64>
    %139 = addi %137, %138 {handshake.bb = 9 : ui32, handshake.name = "addi22"} : <i64>
    %140 = addi %136, %139 {handshake.bb = 9 : ui32, handshake.name = "addi23"} : <i64>
    %141 = addi %140, %119 {handshake.bb = 9 : ui32, handshake.name = "addi7"} : <i64>
    %142 = trunci %141 {handshake.bb = 9 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_52, %dataResult_53 = load[%142] %2#1 {handshake.bb = 9 : ui32, handshake.name = "load5"} : <i32>, <i32>, <i32>, <i32>
    %143 = extui %116 {handshake.bb = 9 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %144 = shli %143, %132 {handshake.bb = 9 : ui32, handshake.name = "shli12"} : <i64>
    %145 = shli %143, %130 {handshake.bb = 9 : ui32, handshake.name = "shli13"} : <i64>
    %146 = addi %144, %145 {handshake.bb = 9 : ui32, handshake.name = "addi24"} : <i64>
    %147 = shli %143, %128 {handshake.bb = 9 : ui32, handshake.name = "shli14"} : <i64>
    %148 = shli %143, %126 {handshake.bb = 9 : ui32, handshake.name = "shli15"} : <i64>
    %149 = addi %147, %148 {handshake.bb = 9 : ui32, handshake.name = "addi25"} : <i64>
    %150 = addi %146, %149 {handshake.bb = 9 : ui32, handshake.name = "addi26"} : <i64>
    %151 = addi %150, %120 {handshake.bb = 9 : ui32, handshake.name = "addi8"} : <i64>
    %152 = trunci %151 {handshake.bb = 9 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_54, %dataResult_55 = load[%152] %2#2 {handshake.bb = 9 : ui32, handshake.name = "load6"} : <i32>, <i32>, <i32>, <i32>
    %153 = muli %dataResult_53, %dataResult_55 {handshake.bb = 9 : ui32, handshake.name = "muli4"} : <i32>
    %154 = addi %115, %153 {handshake.bb = 9 : ui32, handshake.name = "addi9"} : <i32>
    %155 = addi %116, %124 {handshake.bb = 9 : ui32, handshake.name = "addi10"} : <i32>
    %156 = cmpi ult, %155, %122 {handshake.bb = 9 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_56, %falseResult_57 = cond_br %156, %154 {handshake.bb = 9 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_58, %falseResult_59 = cond_br %156, %155 {handshake.bb = 9 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_60, %falseResult_61 = cond_br %156, %117 {handshake.bb = 9 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %156, %118 {handshake.bb = 9 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %156, %119 {handshake.bb = 9 : ui32, handshake.name = "cond_br26"} : <i1>, <i64>
    %trueResult_66, %falseResult_67 = cond_br %156, %120 {handshake.bb = 9 : ui32, handshake.name = "cond_br27"} : <i1>, <i64>
    %trueResult_68, %falseResult_69 = cond_br %156, %result_50 {handshake.bb = 9 : ui32, handshake.name = "cond_br28"} : <i1>, <>
    %157 = merge %falseResult_57 {handshake.bb = 10 : ui32, handshake.name = "merge3"} : <i32>
    %158 = merge %falseResult_61 {handshake.bb = 10 : ui32, handshake.name = "merge4"} : <i32>
    %159 = merge %falseResult_63 {handshake.bb = 10 : ui32, handshake.name = "merge5"} : <i32>
    %result_70, %index_71 = control_merge [%falseResult_69]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    %160 = source {handshake.bb = 10 : ui32, handshake.name = "source22"} : <>
    %161 = constant %160 {handshake.bb = 10 : ui32, handshake.name = "constant35", value = 30 : i32} : <>, <i32>
    %162 = source {handshake.bb = 10 : ui32, handshake.name = "source23"} : <>
    %163 = constant %162 {handshake.bb = 10 : ui32, handshake.name = "constant36", value = 1 : i32} : <>, <i32>
    %164 = source {handshake.bb = 10 : ui32, handshake.name = "source24"} : <>
    %165 = constant %164 {handshake.bb = 10 : ui32, handshake.name = "constant37", value = 4 : i64} : <>, <i64>
    %166 = source {handshake.bb = 10 : ui32, handshake.name = "source25"} : <>
    %167 = constant %166 {handshake.bb = 10 : ui32, handshake.name = "constant38", value = 3 : i64} : <>, <i64>
    %168 = source {handshake.bb = 10 : ui32, handshake.name = "source26"} : <>
    %169 = constant %168 {handshake.bb = 10 : ui32, handshake.name = "constant39", value = 2 : i64} : <>, <i64>
    %170 = source {handshake.bb = 10 : ui32, handshake.name = "source27"} : <>
    %171 = constant %170 {handshake.bb = 10 : ui32, handshake.name = "constant40", value = 1 : i64} : <>, <i64>
    %172 = extui %158 {handshake.bb = 10 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %173 = extui %159 {handshake.bb = 10 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %174 = shli %172, %171 {handshake.bb = 10 : ui32, handshake.name = "shli16"} : <i64>
    %175 = shli %172, %169 {handshake.bb = 10 : ui32, handshake.name = "shli17"} : <i64>
    %176 = addi %174, %175 {handshake.bb = 10 : ui32, handshake.name = "addi27"} : <i64>
    %177 = shli %172, %167 {handshake.bb = 10 : ui32, handshake.name = "shli18"} : <i64>
    %178 = shli %172, %165 {handshake.bb = 10 : ui32, handshake.name = "shli19"} : <i64>
    %179 = addi %177, %178 {handshake.bb = 10 : ui32, handshake.name = "addi28"} : <i64>
    %180 = addi %176, %179 {handshake.bb = 10 : ui32, handshake.name = "addi29"} : <i64>
    %181 = addi %180, %173 {handshake.bb = 10 : ui32, handshake.name = "addi11"} : <i64>
    %182 = trunci %181 {handshake.bb = 10 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_72, %dataResult_73 = store[%182] %157 {handshake.bb = 10 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store7"} : <i32>, <i32>, <i32>, <i32>
    %183 = extui %159 {handshake.bb = 10 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %184 = extui %158 {handshake.bb = 10 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %185 = shli %183, %171 {handshake.bb = 10 : ui32, handshake.name = "shli20"} : <i64>
    %186 = shli %183, %169 {handshake.bb = 10 : ui32, handshake.name = "shli21"} : <i64>
    %187 = addi %185, %186 {handshake.bb = 10 : ui32, handshake.name = "addi30"} : <i64>
    %188 = shli %183, %167 {handshake.bb = 10 : ui32, handshake.name = "shli22"} : <i64>
    %189 = shli %183, %165 {handshake.bb = 10 : ui32, handshake.name = "shli23"} : <i64>
    %190 = addi %188, %189 {handshake.bb = 10 : ui32, handshake.name = "addi31"} : <i64>
    %191 = addi %187, %190 {handshake.bb = 10 : ui32, handshake.name = "addi32"} : <i64>
    %192 = addi %191, %184 {handshake.bb = 10 : ui32, handshake.name = "addi12"} : <i64>
    %193 = trunci %192 {handshake.bb = 10 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_74, %dataResult_75 = store[%193] %157 {handshake.bb = 10 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : <i32>, <i32>, <i32>, <i32>
    %194 = addi %159, %163 {handshake.bb = 10 : ui32, handshake.name = "addi13"} : <i32>
    %195 = cmpi ult, %194, %161 {handshake.bb = 10 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_76, %falseResult_77 = cond_br %195, %194 {handshake.bb = 10 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_78, %falseResult_79 = cond_br %195, %158 {handshake.bb = 10 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_80, %falseResult_81 = cond_br %195, %result_70 {handshake.bb = 10 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %196 = merge %falseResult_79 {handshake.bb = 11 : ui32, handshake.name = "merge6"} : <i32>
    %result_82, %index_83 = control_merge [%falseResult_81]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    %197 = source {handshake.bb = 11 : ui32, handshake.name = "source28"} : <>
    %198 = constant %197 {handshake.bb = 11 : ui32, handshake.name = "constant41", value = 30 : i32} : <>, <i32>
    %199 = source {handshake.bb = 11 : ui32, handshake.name = "source29"} : <>
    %200 = constant %199 {handshake.bb = 11 : ui32, handshake.name = "constant42", value = 1 : i32} : <>, <i32>
    %201 = addi %196, %200 {handshake.bb = 11 : ui32, handshake.name = "addi14"} : <i32>
    %202 = cmpi ult, %201, %198 {handshake.bb = 11 : ui32, handshake.name = "cmpi6"} : <i32>
    %trueResult_84, %falseResult_85 = cond_br %202, %201 {handshake.bb = 11 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %trueResult_86, %falseResult_87 = cond_br %202, %result_82 {handshake.bb = 11 : ui32, handshake.name = "cond_br33"} : <i1>, <>
    %result_88, %index_89 = control_merge [%falseResult_87]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>] to <>, <i1>
    end {handshake.bb = 12 : ui32, handshake.name = "end0"} %memEnd, %1, %0#1, %arg6 : <>, <>, <>, <>
  }
}

