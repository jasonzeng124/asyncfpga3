module {
  handshake.func @threshold(%arg0: !handshake.channel<i32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: memref<1000xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["th", "red", "green", "blue", "red_start", "green_start", "blue_start", "start"], resNames = ["red_end", "green_end", "blue_end", "end"]} {
    %0:3 = fork [3] %arg7 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg3 : memref<1000xi32>] (%arg6, %14#0, %addressResult_2, %22#0, %addressResult_14, %dataResult_15, %41#2)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2:2 = lsq[%arg2 : memref<1000xi32>] (%arg5, %14#2, %addressResult_0, %22#2, %addressResult_12, %dataResult_13, %41#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq4"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3:2 = lsq[%arg1 : memref<1000xi32>] (%arg4, %14#3, %addressResult, %22#3, %addressResult_10, %dataResult_11, %41#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq5"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %4 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %5 = br %4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %6 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i10>
    %7 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %8 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %9 = mux %13#0 [%6, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %10:4 = fork [4] %9 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %11 = mux %13#1 [%7, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12:2 = fork [2] %11 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %result, %index = control_merge [%8, %trueResult_22]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %14:4 = lazy_fork [4] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %addressResult, %dataResult = load[%10#2] %3#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_0, %dataResult_1 = load[%10#1] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %15 = addi %dataResult, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %addressResult_2, %dataResult_3 = load[%10#0] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %16 = addi %15, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %17 = cmpi sgt, %16, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %18:3 = fork [3] %17 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %18#2, %12#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %18#0, %10#3 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i10>
    %trueResult_6, %falseResult_7 = cond_br %18#1, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %19 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %20 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i10>
    %21:4 = fork [4] %20 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i10>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink0"} : <i1>
    %22:5 = lazy_fork [5] %result_8 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %23 = constant %22#4 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %24:3 = fork [3] %23 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %addressResult_10, %dataResult_11 = store[%21#2] %24#2 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store3"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_12, %dataResult_13 = store[%21#1] %24#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_14, %dataResult_15 = store[%21#0] %24#0 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : <i10>, <i32>, <i10>, <i32>
    %25 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %26 = br %21#3 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i10>
    %27 = br %22#1 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %28 = mux %32#1 [%trueResult, %25] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %32#0 [%trueResult_4, %26] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %30 = extui %29 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i10> to <i11>
    %31 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i11} : <>, <i11>
    %result_16, %index_17 = control_merge [%trueResult_6, %27]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %32:2 = fork [2] %index_17 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i1>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %35 = addi %30, %31 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i11>
    %36:2 = fork [2] %35 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i11>
    %37 = trunci %36#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %38 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1000 : i11} : <>, <i11>
    %39 = cmpi ult, %36#1, %38 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i11>
    %40:3 = fork [3] %39 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %40#0, %37 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i10>
    sink %falseResult_19 {handshake.name = "sink1"} : <i10>
    %trueResult_20, %falseResult_21 = cond_br %40#1, %28 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_21 {handshake.name = "sink2"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %40#2, %result_16 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_25 {handshake.name = "sink3"} : <i1>
    %41:3 = fork [3] %result_24 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %3#1, %2#1, %1#1, %0#1 : <>, <>, <>, <>
  }
}

