module {
  handshake.func @wrap_if(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg5 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%28, %addressResult_8, %dataResult_9) %69#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i32>) -> ()
    %1:2 = lsq[%arg0 : memref<100xi32>] (%arg3, %11#0, %addressResult, %50#0, %addressResult_12, %dataResult_13, %69#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i7>
    %5 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %7 = mux %10#0 [%4, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %9 = mux %10#1 [%5, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %11:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8#0] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %16:3 = fork [3] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %17 = shli %16#0, %13 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %18 = addi %16#1, %17 {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[3,-4,5]"}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %19 = cmpi sgt, %16#2, %15 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %20:4 = fork [4] %19 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %20#3, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %20#0, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i7>
    %trueResult_2, %falseResult_3 = cond_br %20#2, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %20#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %21 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %23 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i7>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i7>
    %25 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %result_6, %index_7 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink0"} : <i1>
    %27:2 = fork [2] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <>
    %28 = constant %27#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 3 : i32} : <>, <i32>
    %33 = addi %26#1, %22#1 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %34:2 = fork [2] %33 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i32>
    %35 = shli %34#1, %30 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %36 = shli %34#0, %32 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %37 = addi %35, %36 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_8, %dataResult_9 = store[%24#0] %37 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %38 = br %26#0 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %39 = br %22#0 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %40 = br %24#1 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i7>
    %41 = br %27#1 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <>
    %42 = mux %49#1 [%falseResult_3, %38] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %43 = mux %49#2 [%falseResult, %39] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %44:2 = fork [2] %43 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %45 = mux %49#0 [%falseResult_1, %40] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i7>, <i7>] to <i7>
    %46:2 = fork [2] %45 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i7>
    %47 = extui %46#1 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i7> to <i8>
    %48 = constant %53#0 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 1 : i8} : <>, <i8>
    %result_10, %index_11 = control_merge [%falseResult_5, %41]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %49:3 = fork [3] %index_11 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i1>
    %50:2 = lazy_fork [2] %result_10 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork1"} : <>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %53:2 = fork [2] %52 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <>
    %54 = constant %53#1 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %55 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %56 = constant %55 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 3 : i32} : <>, <i32>
    %57 = subi %42, %44#1 {handshake.bb = 3 : ui32, handshake.name = "subi0"} : <i32>
    %58:3 = fork [3] %57 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i32>
    %59 = shli %58#2, %54 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i32>
    %60 = shli %58#1, %56 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i32>
    %61 = addi %59, %60 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %62 = addi %58#0, %61 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %addressResult_12, %dataResult_13 = store[%46#0] %62 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store2"} : <i7>, <i32>, <i7>, <i32>
    %63 = addi %47, %48 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i8>
    %64:2 = fork [2] %63 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i8>
    %65 = trunci %64#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %66 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 100 : i8} : <>, <i8>
    %67 = cmpi ult, %64#1, %66 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i8>
    %68:3 = fork [3] %67 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %68#0, %65 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i7>
    sink %falseResult_15 {handshake.name = "sink1"} : <i7>
    %trueResult_16, %falseResult_17 = cond_br %68#1, %44#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink2"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %68#2, %50#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_21 {handshake.name = "sink3"} : <i1>
    %69:2 = fork [2] %result_20 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

