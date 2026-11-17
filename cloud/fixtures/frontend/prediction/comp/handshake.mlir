module {
  handshake.func @prediction(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: !handshake.channel<f32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %memEnd = mem_controller[%arg1 : memref<100xf32>] %arg4 (%5, %addressResult_0, %dataResult_1) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %0:2 = lsq[%arg0 : memref<100xf32>] (%arg3, %result, %addressResult, %addressResult_2, %dataResult_3, %result_8)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %4 = br %arg5 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %6 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%4, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 5.000000e+00 : f32} : <>, <f32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 100 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 1.000000e+01 : f32} : <>, <f32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 1.000000e+00 : f32} : <>, <f32>
    %18 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %19 = trunci %18 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%19] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %20 = addf %dataResult, %17 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %21 = mulf %20, %15 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %22 = fptosi %21 {handshake.bb = 1 : ui32, handshake.name = "fptosi0"} : <f32> to <i32>
    %23 = cmpi eq, %22, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %24 = select %23[%11, %dataResult] {dynamatic.predict = {location = "start", marker = 1 : i32, type = "float", values = "[7.0,7.5]"}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %25 = addf %24, %7 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf1"} : <f32>
    %26 = mulf %25, %15 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf1"} : <f32>
    %27 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %28 = trunci %27 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = store[%28] %26 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <f32>, <i32>, <f32>
    %29 = subf %24, %7 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %30 = mulf %29, %15 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf2"} : <f32>
    %31 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %32 = trunci %31 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = store[%32] %30 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <f32>, <i32>, <f32>
    %33 = addi %6, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %34 = cmpi ult, %33, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult, %falseResult = cond_br %34, %33 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %34, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_6, %falseResult_7 = cond_br %34, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg5 : <>, <>, <>
  }
}

