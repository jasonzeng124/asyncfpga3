module {
  handshake.func @trisolv(%arg0: memref<1000xi32>, %arg1: memref<1000000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "A", "c", "x_start", "A_start", "c_start", "start"], resNames = ["x_end", "A_end", "c_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%addressResult) %result_36 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg1 : memref<1000000xi32>] %arg4 (%addressResult_12, %addressResult_28) %result_36 {connectedBlocks = [2 : i32, 3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0:4 = lsq[%arg0 : memref<1000xi32>] (%arg3, %result, %addressResult_2, %dataResult_3, %result_8, %addressResult_10, %addressResult_14, %addressResult_16, %dataResult_17, %result_24, %addressResult_26, %addressResult_30, %dataResult_31, %result_36)  {groupSizes = [1 : i32, 3 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %4 = mux %index [%2, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_34]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = trunci %6 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%7] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %8 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = trunci %8 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = store[%9] %dataResult {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %10 = cmpi ugt, %4, %5 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %10, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %10, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %11 = mux %index_9 [%trueResult, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_9 [%trueResult_4, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_8, %index_9 = control_merge [%trueResult_6, %trueResult_22]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 9 : i64} : <>, <i64>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 8 : i64} : <>, <i64>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 7 : i64} : <>, <i64>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 6 : i64} : <>, <i64>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 5 : i64} : <>, <i64>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant17", value = 3 : i64} : <>, <i64>
    %27 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %28 = trunci %27 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%28] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %29 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %30 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %31 = shli %29, %26 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %32 = shli %29, %24 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %33 = shli %29, %22 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %34 = addi %32, %33 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i64>
    %35 = addi %31, %34 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %36 = shli %29, %20 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %37 = shli %29, %18 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %38 = shli %29, %16 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %39 = addi %37, %38 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %40 = addi %36, %39 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %41 = addi %35, %40 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %42 = addi %41, %30 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %43 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%43] %outputs_0#0 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %44 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %45 = trunci %44 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = load[%45] %0#1 {handshake.bb = 2 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %46 = muli %dataResult_13, %dataResult_15 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %47 = subi %dataResult_11, %46 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %48 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = store[%49] %47 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %50 = addi %11, %14 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %51 = cmpi ult, %50, %12 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %51, %50 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %51, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %51, %result_8 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %52 = mux %index_25 [%falseResult_5, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%falseResult_7, %falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %53 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %54 = constant %53 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1000 : i32} : <>, <i32>
    %55 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %56 = constant %55 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %57 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %58 = constant %57 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 9 : i64} : <>, <i64>
    %59 = source {handshake.bb = 3 : ui32, handshake.name = "source10"} : <>
    %60 = constant %59 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 8 : i64} : <>, <i64>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source11"} : <>
    %62 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant22", value = 7 : i64} : <>, <i64>
    %63 = source {handshake.bb = 3 : ui32, handshake.name = "source12"} : <>
    %64 = constant %63 {handshake.bb = 3 : ui32, handshake.name = "constant23", value = 6 : i64} : <>, <i64>
    %65 = source {handshake.bb = 3 : ui32, handshake.name = "source13"} : <>
    %66 = constant %65 {handshake.bb = 3 : ui32, handshake.name = "constant24", value = 5 : i64} : <>, <i64>
    %67 = source {handshake.bb = 3 : ui32, handshake.name = "source14"} : <>
    %68 = constant %67 {handshake.bb = 3 : ui32, handshake.name = "constant25", value = 3 : i64} : <>, <i64>
    %69 = extui %52 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %70 = trunci %69 {handshake.bb = 3 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_26, %dataResult_27 = load[%70] %0#2 {handshake.bb = 3 : ui32, handshake.name = "load6"} : <i32>, <i32>, <i32>, <i32>
    %71 = extui %52 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %72 = extui %52 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %73 = shli %71, %68 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %74 = shli %71, %66 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %75 = shli %71, %64 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %76 = addi %74, %75 {handshake.bb = 3 : ui32, handshake.name = "addi9"} : <i64>
    %77 = addi %73, %76 {handshake.bb = 3 : ui32, handshake.name = "addi10"} : <i64>
    %78 = shli %71, %62 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %79 = shli %71, %60 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %80 = shli %71, %58 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %81 = addi %79, %80 {handshake.bb = 3 : ui32, handshake.name = "addi11"} : <i64>
    %82 = addi %78, %81 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i64>
    %83 = addi %77, %82 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i64>
    %84 = addi %83, %72 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i64>
    %85 = trunci %84 {handshake.bb = 3 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_28, %dataResult_29 = load[%85] %outputs_0#1 {handshake.bb = 3 : ui32, handshake.name = "load7"} : <i32>, <i32>, <i32>, <i32>
    %86 = divsi %dataResult_27, %dataResult_29 {handshake.bb = 3 : ui32, handshake.name = "divsi0"} : <i32>
    %87 = extui %52 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %88 = trunci %87 {handshake.bb = 3 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = store[%88] %86 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : <i32>, <i32>, <i32>, <i32>
    %89 = addi %52, %56 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %90 = cmpi ult, %89, %54 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_32, %falseResult_33 = cond_br %90, %89 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %90, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %result_36, %index_37 = control_merge [%falseResult_35]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#3, %memEnd_1, %memEnd, %arg6 : <>, <>, <>, <>
  }
}

