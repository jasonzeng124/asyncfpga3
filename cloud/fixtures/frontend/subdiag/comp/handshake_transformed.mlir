module {
  handshake.func @subdiag(%arg0: memref<1000xf32>, %arg1: memref<1000xf32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["d", "e", "d_start", "e_start", "start"], resNames = ["out0", "d_end", "e_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xf32>] %arg3 (%addressResult_4) %28#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<1000xf32>] %arg2 (%addressResult, %addressResult_2) %28#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6:4 = fork [4] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %7 = trunci %6#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %8 = constant %15#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i10} : <>, <i10>
    %9 = trunci %6#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %result, %index = control_merge [%4, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 998 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1.000000e-03 : f32} : <>, <f32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %16 = constant %15#1 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %17 = addi %7, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult_2, %dataResult_3 = load[%17] %outputs_0#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %18 = addf %dataResult, %dataResult_3 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %19 = addi %6#3, %16 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %21 = trunci %20#0 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %addressResult_4, %dataResult_5 = load[%21] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %22 = mulf %18, %13 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %23 = cmpf ugt, %dataResult_5, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %24 = cmpi ult, %6#2, %11 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %25 = andi %24, %23 {dynamatic.speculate = {max_predictions = 9 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %26:2 = fork [2] %25 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %26#1, %20#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %26#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %27 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink0"} : <i1>
    %28:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %27, %memEnd_1, %memEnd, %0#1 : <i32>, <>, <>, <>
  }
}

