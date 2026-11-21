module {
  handshake.func @test_memory_8(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:4 = lsq[%arg0 : memref<4xi32>] (%arg2, %16#0, %addressResult, %addressResult_4, %33#0, %addressResult_14, %addressResult_16, %dataResult_17, %addressResult_18, %dataResult_19, %result_28)  {groupSizes = [2 : i32, 3 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = -2 : i2} : <>, <i2>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink0"} : <i2>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i2> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %8 = mux %15#0 [%7, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %11 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i2} : <>, <i2>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %13 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = -2 : i2} : <>, <i2>
    %14 = mux %15#1 [%trueResult_0, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_26]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %15:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %16:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = -5 : i32} : <>, <i32>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %21 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i2>
    %addressResult, %dataResult = load[%21] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %22 = addi %12, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i2>
    %addressResult_4, %dataResult_5 = load[%22] %2#1 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %23 = addi %dataResult, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %24 = cmpi sgt, %23, %18 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25:3 = fork [3] %24 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %25#2, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %25#1, %9#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %25#0, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %26 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %27 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %28:4 = fork [4] %27 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %29 = trunci %28#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i2>
    %30 = constant %35 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = -1 : i2} : <>, <i2>
    %31 = trunci %28#1 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i32> to <i2>
    %32 = trunci %28#2 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i32> to <i2>
    %result_12, %index_13 = control_merge [%trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_13 {handshake.name = "sink2"} : <i1>
    %33:3 = lazy_fork [3] %result_12 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %34 = constant %33#2 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %35 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %addressResult_14, %dataResult_15 = load[%32] %2#2 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : false}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : <i2>, <i32>, <i2>, <i32>
    %36 = addi %29, %30 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i2>
    %addressResult_16, %dataResult_17 = store[%36] %dataResult_15 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %addressResult_18, %dataResult_19 = store[%31] %34 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : <i2>, <i32>, <i2>, <i32>
    %37 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %38 = br %28#3 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %39 = br %33#1 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <>
    %40 = mux %43#0 [%falseResult_7, %37] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %41:2 = fork [2] %40 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i32>
    %42 = mux %43#1 [%falseResult_9, %38] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_11, %39]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %43:2 = fork [2] %index_21 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %46 = addi %42, %45 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %47:2 = fork [2] %46 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %48 = cmpi slt, %47#1, %41#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %49:3 = fork [3] %48 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_22, %falseResult_23 = cond_br %49#2, %47#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink3"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %49#1, %41#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_25 {handshake.name = "sink4"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %49#0, %result_20 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_28, %index_29 = control_merge [%falseResult_3, %falseResult_27]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %index_29 {handshake.name = "sink5"} : <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %2#3, %0#1 : <>, <>
  }
}

