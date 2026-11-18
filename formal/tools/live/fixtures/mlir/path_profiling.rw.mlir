module {
  handshake.func @path_profiling(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "var", "a_start", "b_start", "var_start", "start"], resNames = ["a_end", "b_end", "var_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs:2, %memEnd = mem_controller[%arg2 : memref<20xi32>] %arg5 (%addressResult, %addressResult_12) %61#2 {connectedBlocks = [1 : i32, 4 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i5>, !handshake.channel<i5>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = lsq[%arg1 : memref<20xi32>] (%arg4, %40#0, %addressResult_20, %dataResult_21, %46#0, %addressResult_24, %dataResult_25, %61#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>) -> !handshake.control<>
    %2 = lsq[%arg0 : memref<20xi32>] (%arg3, %19#0, %addressResult_4, %dataResult_5, %25#0, %addressResult_8, %dataResult_9, %61#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>) -> !handshake.control<>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i5>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %7 = mux %index [%5, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%6, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %addressResult, %dataResult = load[%8#0] %outputs#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %11 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i1>
    %12 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %13 = andi %11, %12 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %14 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %15 = cmpi eq, %13, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i1>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %16#0, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i5>
    %trueResult_0, %falseResult_1 = cond_br %16#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %17 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i5>
    %18:2 = fork [2] %17 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %result_2, %index_3 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_3 {handshake.name = "sink0"} : <i1>
    %19:3 = lazy_fork [3] %result_2 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork0"} : <>
    %20 = constant %19#2 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 2 : i32} : <>, <i32>
    %addressResult_4, %dataResult_5 = store[%18#0] %20 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i5>, <i32>, <i5>, <i32>
    %21 = br %18#1 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i5>
    %22 = br %19#1 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <>
    %23 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i5>
    %24:2 = fork [2] %23 {handshake.bb = 3 : ui32, handshake.name = "fork4"} : <i5>
    %result_6, %index_7 = control_merge [%falseResult_1]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %25:3 = lazy_fork [3] %result_6 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork1"} : <>
    %26 = constant %25#2 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 3 : i32} : <>, <i32>
    %addressResult_8, %dataResult_9 = store[%24#0] %26 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store2"} : <i5>, <i32>, <i5>, <i32>
    %27 = br %24#1 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <i5>
    %28 = br %25#1 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <>
    %29 = mux %index_11 [%21, %27] {handshake.bb = 4 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %30:2 = fork [2] %29 {handshake.bb = 4 : ui32, handshake.name = "fork5"} : <i5>
    %result_10, %index_11 = control_merge [%22, %28]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %31 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %32 = constant %31 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %33 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %34 = constant %33 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %addressResult_12, %dataResult_13 = load[%30#0] %outputs#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i5>, <i32>, <i5>, <i32>
    %35 = remsi %dataResult_13, %32 {handshake.bb = 4 : ui32, handshake.name = "remsi0"} : <i32>
    %36 = cmpi eq, %35, %34 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %37:2 = fork [2] %36 {handshake.bb = 4 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %37#0, %30#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_16, %falseResult_17 = cond_br %37#1, %result_10 {handshake.bb = 4 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %38 = merge %trueResult_14 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i5>
    %39:2 = fork [2] %38 {handshake.bb = 5 : ui32, handshake.name = "fork7"} : <i5>
    %result_18, %index_19 = control_merge [%trueResult_16]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink2"} : <i1>
    %40:3 = lazy_fork [3] %result_18 {handshake.bb = 5 : ui32, handshake.name = "lazy_fork2"} : <>
    %41 = constant %40#2 {handshake.bb = 5 : ui32, handshake.name = "constant11", value = 2 : i32} : <>, <i32>
    %addressResult_20, %dataResult_21 = store[%39#0] %41 {handshake.bb = 5 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store4"} : <i5>, <i32>, <i5>, <i32>
    %42 = br %39#1 {handshake.bb = 5 : ui32, handshake.name = "br11"} : <i5>
    %43 = br %40#1 {handshake.bb = 5 : ui32, handshake.name = "br12"} : <>
    %44 = merge %falseResult_15 {handshake.bb = 6 : ui32, handshake.name = "merge3"} : <i5>
    %45:2 = fork [2] %44 {handshake.bb = 6 : ui32, handshake.name = "fork8"} : <i5>
    %result_22, %index_23 = control_merge [%falseResult_17]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink3"} : <i1>
    %46:3 = lazy_fork [3] %result_22 {handshake.bb = 6 : ui32, handshake.name = "lazy_fork3"} : <>
    %47 = constant %46#2 {handshake.bb = 6 : ui32, handshake.name = "constant12", value = 3 : i32} : <>, <i32>
    %addressResult_24, %dataResult_25 = store[%45#0] %47 {handshake.bb = 6 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : <i5>, <i32>, <i5>, <i32>
    %48 = br %45#1 {handshake.bb = 6 : ui32, handshake.name = "br13"} : <i5>
    %49 = br %46#1 {handshake.bb = 6 : ui32, handshake.name = "br14"} : <>
    %50 = mux %index_27 [%42, %48] {handshake.bb = 7 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %51 = extui %50 {handshake.bb = 7 : ui32, handshake.name = "extui7"} : <i5> to <i6>
    %52 = constant %54 {handshake.bb = 7 : ui32, handshake.name = "constant4", value = 1 : i6} : <>, <i6>
    %result_26, %index_27 = control_merge [%43, %49]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %53 = source {handshake.bb = 7 : ui32, handshake.name = "source4"} : <>
    %54 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %55 = addi %51, %52 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i6>
    %56:2 = fork [2] %55 {handshake.bb = 7 : ui32, handshake.name = "fork9"} : <i6>
    %57 = trunci %56#0 {handshake.bb = 7 : ui32, handshake.name = "trunci1"} : <i6> to <i5>
    %58 = constant %53 {handshake.bb = 7 : ui32, handshake.name = "constant15", value = 20 : i6} : <>, <i6>
    %59 = cmpi ult, %56#1, %58 {handshake.bb = 7 : ui32, handshake.name = "cmpi2"} : <i6>
    %60:2 = fork [2] %59 {handshake.bb = 7 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult_28, %falseResult_29 = cond_br %60#0, %57 {handshake.bb = 7 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    sink %falseResult_29 {handshake.name = "sink4"} : <i5>
    %trueResult_30, %falseResult_31 = cond_br %60#1, %result_26 {handshake.bb = 7 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_32, %index_33 = control_merge [%falseResult_31]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    sink %index_33 {handshake.name = "sink5"} : <i1>
    %61:3 = fork [3] %result_32 {handshake.bb = 8 : ui32, handshake.name = "fork11"} : <>
    end {handshake.bb = 8 : ui32, handshake.name = "end0"} %2, %1, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

