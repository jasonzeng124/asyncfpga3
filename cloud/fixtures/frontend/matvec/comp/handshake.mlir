module {
  handshake.func @matvec(%arg0: memref<10000xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["m", "v", "out", "m_start", "v_start", "out_start", "start"], resNames = ["out0", "m_end", "v_end", "out_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<100xi32>] %arg5 (%38, %addressResult_17, %dataResult_18) %result_25 {connectedBlocks = [3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult) %result_25 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<10000xi32>] %arg3 (%addressResult_5) %result_25 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %3 = mux %index [%1, %trueResult_19] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_21]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %7 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %8 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i64>
    %9 = br %result {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %10 = mux %index_4 [%6, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index_4 [%6, %trueResult_7] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_4 [%7, %trueResult_9] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_4 [%8, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_3, %index_4 = control_merge [%9, %trueResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 100 : i32} : <>, <i32>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 6 : i64} : <>, <i64>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 5 : i64} : <>, <i64>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i64} : <>, <i64>
    %24 = extui %10 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %25 = trunci %24 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%25] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %26 = extui %10 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %27 = shli %13, %23 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %28 = shli %13, %21 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %29 = shli %13, %19 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %30 = addi %28, %29 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i64>
    %31 = addi %27, %30 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %32 = addi %31, %26 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %33 = trunci %32 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = load[%33] %outputs_1 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %34 = muli %dataResult, %dataResult_6 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %35 = addi %11, %34 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %36 = addi %10, %17 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %37 = cmpi ult, %36, %15 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %37, %36 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %37, %35 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %37, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %37, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_13, %falseResult_14 = cond_br %37, %result_3 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %38 = constant %result_15 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %39 = merge %falseResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %40 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %41 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %42 = constant %41 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 100 : i32} : <>, <i32>
    %43 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %44 = constant %43 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %45 = extui %40 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %46 = trunci %45 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_17, %dataResult_18 = store[%46] %39 {handshake.bb = 3 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %47 = addi %40, %44 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %48 = cmpi ult, %47, %42 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_19, %falseResult_20 = cond_br %48, %47 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_21, %falseResult_22 = cond_br %48, %result_15 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %trueResult_23, %falseResult_24 = cond_br %48, %39 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %49 = merge %falseResult_24 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_25, %index_26 = control_merge [%falseResult_22]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %49, %memEnd_2, %memEnd_0, %memEnd, %arg6 : <i32>, <>, <>, <>, <>
  }
}

