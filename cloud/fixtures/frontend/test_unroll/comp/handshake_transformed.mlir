module {
  handshake.func @test_unroll(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "result", "A_start", "B_start", "C_start", "result_start", "start"], resNames = ["A_end", "B_end", "C_end", "result_end", "end"]} {
    %0:4 = fork [4] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg3 : memref<20xi32>] %arg7 (%28, %addressResult_19, %dataResult_20) %38#4 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<20xi32>] %arg6 (%addressResult_17) %38#3 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<20xi32>] %arg5 (%addressResult_5) %38#2 {connectedBlocks = [1 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg0 : memref<20xi32>] %arg4 (%addressResult) %38#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i5>) -> !handshake.channel<i32>
    %1:2 = lsq[%2 : memref<20xi32>] (%0#1, %11#0, %addressResult_7, %dataResult_8, %27#0, %addressResult_15, %38#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    sink %1#1 {handshake.name = "sink0"} : <>
    %2 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<0> : memref<20xi32>} : () -> memref<20xi32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant8", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i5>
    %6 = br %0#3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %index [%5, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %8:4 = fork [4] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %9 = extui %8#3 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i5> to <i6>
    %10 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 1 : i6} : <>, <i6>
    %result, %index = control_merge [%6, %trueResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%8#2] %outputs_3 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %addressResult_5, %dataResult_6 = load[%8#1] %outputs_1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %14 = muli %dataResult, %dataResult_6 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %addressResult_7, %dataResult_8 = store[%8#0] %14 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i5>, <i32>, <i5>, <i32>
    %15 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i6>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i6>
    %17 = trunci %16#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i6> to <i5>
    %18 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 20 : i6} : <>, <i6>
    %19 = cmpi ult, %16#1, %18 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i6>
    %20:3 = fork [3] %19 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %trueResult, %falseResult = cond_br %20#0, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink1"} : <i5>
    %trueResult_9, %falseResult_10 = cond_br %20#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %21 = constant %11#2 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = false} : <>, <i1>
    %trueResult_11, %falseResult_12 = cond_br %20#2, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %trueResult_11 {handshake.name = "sink2"} : <i1>
    %22 = extui %falseResult_12 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i1> to <i5>
    %23 = mux %index_14 [%22, %trueResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %24:4 = fork [4] %23 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %25 = extui %24#3 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i5> to <i6>
    %26 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i6} : <>, <i6>
    %result_13, %index_14 = control_merge [%falseResult_10, %trueResult_23]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %27:3 = fork [3] %result_13 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    %28 = constant %27#1 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %addressResult_15, %dataResult_16 = load[%24#2] %1#0 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i5>, <i32>, <i5>, <i32>
    %addressResult_17, %dataResult_18 = load[%24#1] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i5>, <i32>, <i5>, <i32>
    %31 = muli %dataResult_16, %dataResult_18 {handshake.bb = 2 : ui32, handshake.name = "muli3"} : <i32>
    %addressResult_19, %dataResult_20 = store[%24#0] %31 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : <i5>, <i32>, <i5>, <i32>
    %32 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i6>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i6>
    %34 = trunci %33#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i6> to <i5>
    %35 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 20 : i6} : <>, <i6>
    %36 = cmpi ult, %33#1, %35 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i6>
    %37:2 = fork [2] %36 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_21, %falseResult_22 = cond_br %37#0, %34 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_22 {handshake.name = "sink3"} : <i5>
    %trueResult_23, %falseResult_24 = cond_br %37#1, %27#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_25, %index_26 = control_merge [%falseResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_26 {handshake.name = "sink4"} : <i1>
    %38:5 = fork [5] %result_25 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %0#2 : <>, <>, <>, <>, <>
  }
}

