module {
  handshake.func @nested_conditionals_2(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %21#0, %addressResult, %67#0, %addressResult_16, %dataResult_17, %result_26)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %5 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = 3 : i32} : <>, <i32>
    %7 = shli %1#2, %4 {handshake.bb = 0 : ui32, handshake.name = "shli2"} : <i32>
    %8 = shli %1#1, %6 {handshake.bb = 0 : ui32, handshake.name = "shli3"} : <i32>
    %9 = addi %7, %8 {handshake.bb = 0 : ui32, handshake.name = "addi4"} : <i32>
    %10 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = false} : <>, <i1>
    %11 = br %10 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %12 = extui %11 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i7>
    %13 = br %1#0 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %14 = br %9 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %15 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %16 = mux %20#0 [%12, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i7>
    %18 = mux %20#1 [%13, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %20#2 [%14, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%15, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %20:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %21:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %24:2 = fork [2] %23 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %addressResult, %dataResult = load[%17#0] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %25:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %26 = shli %25#0, %24#1 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %27 = cmpi sgt, %25#1, %24#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %28:6 = fork [6] %27 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %28#5, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %28#4, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %28#0, %17#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i7>
    %trueResult_4, %falseResult_5 = cond_br %28#3, %25#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink0"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %28#2, %26 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %28#1, %21#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %29 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %30:3 = fork [3] %29 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %31 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %32 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i7>
    %33 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %34 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %result_10, %index_11 = control_merge [%trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink1"} : <i1>
    %35 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %36 = constant %35 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 2 : i32} : <>, <i32>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %38 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 5 : i32} : <>, <i32>
    %39 = cmpi sgt, %30#2, %38 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %40 = shli %33, %36 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %41 = addi %34, %30#1 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %42 = select %39[%40, %41] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %43 = br %42 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %44 = br %30#0 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i32>
    %45 = br %31 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <i32>
    %46 = br %32 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i7>
    %47 = br %result_10 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <>
    %48 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %49 = merge %falseResult_1 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %50:2 = fork [2] %49 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i32>
    %51 = merge %falseResult_3 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i7>
    %52 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge8"} : <i32>
    %result_12, %index_13 = control_merge [%falseResult_9]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_13 {handshake.name = "sink2"} : <i1>
    %53 = addi %50#1, %52 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %54 = br %53 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <i32>
    %55 = br %48 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i32>
    %56 = br %50#0 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i32>
    %57 = br %51 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <i7>
    %58 = br %result_12 {handshake.bb = 3 : ui32, handshake.name = "br16"} : <>
    %59 = mux %66#1 [%43, %54] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %60 = mux %66#2 [%44, %55] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %61 = mux %66#3 [%45, %56] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %62 = mux %66#0 [%46, %57] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i7>, <i7>] to <i7>
    %63:2 = fork [2] %62 {handshake.bb = 4 : ui32, handshake.name = "fork9"} : <i7>
    %64 = extui %63#1 {handshake.bb = 4 : ui32, handshake.name = "extui3"} : <i7> to <i8>
    %65 = constant %71 {handshake.bb = 4 : ui32, handshake.name = "constant3", value = 1 : i8} : <>, <i8>
    %result_14, %index_15 = control_merge [%47, %58]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %66:4 = fork [4] %index_15 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i1>
    %67:2 = lazy_fork [2] %result_14 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork1"} : <>
    %68 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %69 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %70 = constant %69 {handshake.bb = 4 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %71 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %72 = addi %59, %70 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i32>
    %addressResult_16, %dataResult_17 = store[%63#0] %72 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %73 = addi %64, %65 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i8>
    %74:2 = fork [2] %73 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i8>
    %75 = trunci %74#0 {handshake.bb = 4 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %76 = constant %68 {handshake.bb = 4 : ui32, handshake.name = "constant4", value = 100 : i8} : <>, <i8>
    %77 = cmpi ult, %74#1, %76 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i8>
    %78:4 = fork [4] %77 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %78#0, %75 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i7>
    sink %falseResult_19 {handshake.name = "sink3"} : <i7>
    %trueResult_20, %falseResult_21 = cond_br %78#1, %60 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_21 {handshake.name = "sink4"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %78#2, %61 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink5"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %78#3, %67#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_26, %index_27 = control_merge [%falseResult_25]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_27 {handshake.name = "sink6"} : <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %2#1, %0#1 : <>, <>
  }
}

