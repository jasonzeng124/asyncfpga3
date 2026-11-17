module {
  handshake.func @prediction(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: !handshake.channel<f32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<100xf32>] %arg4 (%15, %addressResult_0, %dataResult_1) %44#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<f32>) -> ()
    %1:2 = lsq[%arg0 : memref<100xf32>] (%arg3, %14#0, %addressResult, %addressResult_2, %dataResult_3, %44#0)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i7>
    %5 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %7 = mux %13#0 [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %8:4 = fork [4] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %9 = extui %8#3 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i7> to <i8>
    %10 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i8} : <>, <i8>
    %11 = mux %13#1 [%5, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <f32>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %14:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %15 = constant %14#1 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 5.000000e+00 : f32} : <>, <f32>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %21 = constant %20#1 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 100 : i32} : <>, <i32>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %23 = constant %22 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 1.000000e+01 : f32} : <>, <f32>
    %24:3 = fork [3] %23 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <f32>
    %25 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 1.000000e+00 : f32} : <>, <f32>
    %addressResult, %dataResult = load[%8#2] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <f32>, <i7>, <f32>
    %27:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <f32>
    %28 = addf %27#0, %26 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %29 = mulf %28, %24#2 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %30 = fptosi %29 {handshake.bb = 1 : ui32, handshake.name = "fptosi0"} : <f32> to <i32>
    %31 = cmpi eq, %30, %21 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %32 = select %31[%18, %27#1] {dynamatic.predict = {location = "start", marker = 1 : i32, type = "float", values = "[7.0,7.5]"}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %33:2 = fork [2] %32 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <f32>
    %34 = addf %33#1, %12#2 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf1"} : <f32>
    %35 = mulf %34, %24#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf1"} : <f32>
    %addressResult_0, %dataResult_1 = store[%8#1] %35 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i7>, <f32>, <i7>, <f32>
    %36 = subf %33#0, %12#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %37 = mulf %36, %24#0 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf2"} : <f32>
    %addressResult_2, %dataResult_3 = store[%8#0] %37 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i7>, <f32>, <i7>, <f32>
    %38 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i8>
    %39:2 = fork [2] %38 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i8>
    %40 = trunci %39#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %41 = constant %20#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 100 : i8} : <>, <i8>
    %42 = cmpi ult, %39#1, %41 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i8>
    %43:3 = fork [3] %42 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult, %falseResult = cond_br %43#0, %40 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_4, %falseResult_5 = cond_br %43#1, %12#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    sink %falseResult_5 {handshake.name = "sink1"} : <f32>
    %trueResult_6, %falseResult_7 = cond_br %43#2, %14#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink2"} : <i1>
    %44:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

