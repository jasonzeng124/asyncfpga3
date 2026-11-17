module {
  handshake.func @histogram(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: memref<1000xf32>, %arg3: !handshake.channel<i32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["feature", "weight", "hist", "n", "feature_start", "weight_start", "hist_start", "start"], resNames = ["feature_end", "weight_end", "hist_end", "end"]} {
    %0:4 = fork [4] %arg7 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = lsq[%arg2 : memref<1000xf32>] (%arg6, %15#0, %addressResult_8, %addressResult_10, %dataResult_11, %26#2)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xf32>] %arg5 (%addressResult_6) %26#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xi32>] %arg4 (%addressResult) %26#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %8 = mux %14#0 [%7, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %11 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %12 = mux %14#1 [%trueResult_2, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %15:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%11] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %18:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %19 = trunci %18#0 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %20 = trunci %18#1 {handshake.bb = 1 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %addressResult_6, %dataResult_7 = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %addressResult_8, %dataResult_9 = load[%20] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : false}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %21 = addf %dataResult_9, %dataResult_7 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %addressResult_10, %dataResult_11 = store[%19] %21 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i10>, <f32>, <i10>, <f32>
    %22 = addi %9#2, %17 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %24 = cmpi slt, %23#1, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25:3 = fork [3] %24 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %25#2, %23#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink2"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %25#1, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink3"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %25#0, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_5, %falseResult_17]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_19 {handshake.name = "sink4"} : <i1>
    %26:3 = fork [3] %result_18 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %2#1, %0#1 : <>, <>, <>, <>
  }
}

