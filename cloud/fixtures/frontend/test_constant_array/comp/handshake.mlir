module {
  handshake.func @test_constant_array(%arg0: memref<9xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["di", "di_start", "start"], resNames = ["out0", "di_end", "end"]} {
    %outputs, %memEnd = mem_controller[%1 : memref<9xi32>] %arg2 (%addressResult_4) %result_24 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<9xi32>] %arg1 (%addressResult) %result_24 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9]> : tensor<9xi32>} : () -> memref<9xi32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%2, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_22]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %7 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %10 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %11 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %13 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %14 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %15 = mux %index_3 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_3 [%10, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_3 [%11, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_3 [%12, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i64>, <i64>] to <i64>
    %19 = mux %index_3 [%13, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i64>, <i64>] to <i64>
    %result_2, %index_3 = control_merge [%14, %trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 3 : i32} : <>, <i32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i64} : <>, <i64>
    %26 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %27 = shli %18, %25 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %28 = addi %18, %27 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i64>
    %29 = addi %28, %26 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %30 = trunci %29 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%30] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %31 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %32 = shli %19, %25 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %33 = addi %19, %32 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %34 = addi %33, %31 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %35 = trunci %34 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = load[%35] %outputs {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %36 = addi %dataResult, %dataResult_5 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %37 = addi %16, %36 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %38 = addi %15, %23 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i32>
    %39 = cmpi ult, %38, %21 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %39, %38 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %39, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %39, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %39, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_12, %falseResult_13 = cond_br %39, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_14, %falseResult_15 = cond_br %39, %result_2 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %40 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %41 = merge %falseResult_9 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %46 = addi %41, %45 {handshake.bb = 3 : ui32, handshake.name = "addi6"} : <i32>
    %47 = cmpi ult, %46, %43 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %47, %40 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %47, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %47, %result_16 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %48 = merge %falseResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %48, %memEnd_1, %arg2 : <i32>, <>, <>
  }
}

