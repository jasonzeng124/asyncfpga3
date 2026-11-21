module {
  handshake.func @nested_conditionals_1(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %11#0, %addressResult, %61#0, %addressResult_14, %dataResult_15, %result_22)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i7>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %7 = mux %10#0 [%4, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %9 = mux %10#1 [%5, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %11:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 8 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8#0] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %16:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %17 = addi %16#0, %15 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %18 = cmpi sgt, %16#1, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %19:5 = fork [5] %18 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %19#4, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %19#0, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i7>
    %trueResult_2, %falseResult_3 = cond_br %19#3, %17 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %19#2, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_6, %falseResult_7 = cond_br %19#1, %16#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %trueResult_6 {handshake.name = "sink0"} : <i32>
    %20 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %21:3 = fork [3] %20 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %22 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i7>
    %23 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %result_8, %index_9 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 5 : i32} : <>, <i32>
    %29 = cmpi sgt, %21#2, %28 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %30 = shli %24#1, %26 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %31 = addi %24#0, %21#1 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %32 = select %29[%30, %31] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %33 = br %32 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %34 = br %21#0 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %35 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i7>
    %36 = br %result_8 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <>
    %37 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %38:3 = fork [3] %37 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i32>
    %39 = merge %falseResult_1 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i7>
    %40 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %41 = merge %falseResult_3 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_5]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink2"} : <i1>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = -1 : i32} : <>, <i32>
    %44 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %45 = constant %44 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %46 = cmpi eq, %38#2, %45 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %47 = addi %40, %43 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %48 = muli %41, %38#1 {handshake.bb = 3 : ui32, handshake.name = "muli0"} : <i32>
    %49 = select %46[%47, %48] {handshake.bb = 3 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %50 = br %49 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i32>
    %51 = br %38#0 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i32>
    %52 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <i7>
    %53 = br %result_10 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <>
    %54 = mux %60#1 [%33, %50] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %55 = mux %60#2 [%34, %51] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %56 = mux %60#0 [%35, %52] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i7>, <i7>] to <i7>
    %57:2 = fork [2] %56 {handshake.bb = 4 : ui32, handshake.name = "fork8"} : <i7>
    %58 = extui %57#1 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i7> to <i8>
    %59 = constant %65 {handshake.bb = 4 : ui32, handshake.name = "constant2", value = 1 : i8} : <>, <i8>
    %result_12, %index_13 = control_merge [%36, %53]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %60:3 = fork [3] %index_13 {handshake.bb = 4 : ui32, handshake.name = "fork9"} : <i1>
    %61:2 = lazy_fork [2] %result_12 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork1"} : <>
    %62 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %63 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %64 = constant %63 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 3 : i32} : <>, <i32>
    %65 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %66 = addi %54, %64 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_14, %dataResult_15 = store[%57#0] %66 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %67 = addi %58, %59 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i8>
    %68:2 = fork [2] %67 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i8>
    %69 = trunci %68#0 {handshake.bb = 4 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %70 = constant %62 {handshake.bb = 4 : ui32, handshake.name = "constant3", value = 100 : i8} : <>, <i8>
    %71 = cmpi ult, %68#1, %70 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i8>
    %72:3 = fork [3] %71 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %72#0, %69 {handshake.bb = 4 : ui32, handshake.name = "cond_br7"} : <i1>, <i7>
    sink %falseResult_17 {handshake.name = "sink3"} : <i7>
    %trueResult_18, %falseResult_19 = cond_br %72#1, %55 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink4"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %72#2, %61#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink5"} : <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %1#1, %0#1 : <>, <>
  }
}

