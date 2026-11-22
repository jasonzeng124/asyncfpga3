module {
  handshake.func @matrix_power(%arg0: memref<400xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["mat", "row", "col", "a", "mat_start", "row_start", "col_start", "a_start", "start"], resNames = ["mat_end", "row_end", "col_end", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg3 : memref<20xi32>] %arg7 (%addressResult) %result_30 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg2 : memref<20xi32>] %arg6 (%addressResult_6) %result_30 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg1 : memref<20xi32>] %arg5 (%addressResult_10) %result_30 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0:3 = lsq[%arg0 : memref<400xi32>] (%arg4, %result_4, %addressResult_8, %addressResult_12, %addressResult_14, %dataResult_15, %result_30)  {groupSizes = [3 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_28]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = -1 : i32} : <>, <i32>
    %8 = addi %4, %7 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %9 = extui %8 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %11 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %12 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %13 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i64>
    %14 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %15 = br %result {handshake.bb = 1 : ui32, handshake.name = "br8"} : <>
    %16 = mux %index_5 [%11, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_5 [%12, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_5 [%13, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %19 = mux %index_5 [%14, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_4, %index_5 = control_merge [%15, %trueResult_22]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 20 : i32} : <>, <i32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i64} : <>, <i64>
    %28 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%29] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %30 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %31 = trunci %30 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = load[%31] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %32 = extsi %dataResult_7 {handshake.bb = 2 : ui32, handshake.name = "extsi0"} : <i32> to <i64>
    %33 = shli %18, %27 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %34 = shli %18, %25 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %35 = addi %33, %34 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %36 = addi %35, %32 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %37 = trunci %36 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%37] %0#0 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %38 = muli %dataResult, %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %39 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %40 = trunci %39 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%40] %outputs_2 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %41 = extsi %dataResult_11 {handshake.bb = 2 : ui32, handshake.name = "extsi1"} : <i32> to <i64>
    %42 = shli %19, %27 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %43 = shli %19, %25 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %44 = addi %42, %43 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %45 = addi %44, %41 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i64>
    %46 = trunci %45 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%46] %0#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %47 = addi %dataResult_13, %38 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %48 = trunci %45 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = store[%48] %47 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %49 = addi %16, %23 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %50 = cmpi ult, %49, %21 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %50, %49 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %50, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %50, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i64>
    %trueResult_20, %falseResult_21 = cond_br %50, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_22, %falseResult_23 = cond_br %50, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %51 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %53 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 20 : i32} : <>, <i32>
    %54 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %55 = constant %54 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %56 = addi %51, %55 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %57 = cmpi ult, %56, %53 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %57, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %57, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#2, %memEnd_3, %memEnd_1, %memEnd, %arg8 : <>, <>, <>, <>, <>
  }
}

