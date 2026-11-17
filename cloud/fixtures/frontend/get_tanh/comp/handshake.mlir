module {
  handshake.func @get_tanh(%arg0: memref<1000xf32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "addr", "A_start", "addr_start", "start"], resNames = ["A_end", "addr_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult) %result_20 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = lsq[%arg0 : memref<1000xf32>] (%arg2, %result, %addressResult_0, %result_12, %addressResult_14, %dataResult_15, %result_20)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1.000000e+00 : f32} : <>, <f32>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = trunci %6 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%7] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %8 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_0, %dataResult_1 = load[%8] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %9 = cmpf ult, %dataResult_1, %5 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult, %falseResult = cond_br %9, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %9, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %9, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_6, %falseResult_7 = cond_br %9, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %9, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %10 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %11 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %12 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_10, %index_11 = control_merge [%trueResult_6]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 3.70476198 : f32} : <>, <f32>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 19.5238094 : f32} : <>, <f32>
    %17 = mulf %12, %12 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %18 = addf %17, %16 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %19 = mulf %18, %12 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %20 = mulf %19, %12 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf2"} : <f32>
    %21 = addf %20, %14 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %22 = mulf %21, %12 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf3"} : <f32>
    %23 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <f32>
    %24 = br %10 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %25 = br %11 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %26 = br %result_10 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %27 = mux %index_13 [%falseResult_9, %23] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %28 = mux %index_13 [%falseResult, %24] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %index_13 [%falseResult_3, %25] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_12, %index_13 = control_merge [%falseResult_7, %26]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 1000 : i32} : <>, <i32>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %33 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %34 = trunci %29 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_14, %dataResult_15 = store[%34] %27 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <f32>, <i32>, <f32>
    %35 = addi %28, %33 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %36 = cmpi ult, %35, %31 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %36, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %36, %result_12 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg4 : <>, <>, <>
  }
}

