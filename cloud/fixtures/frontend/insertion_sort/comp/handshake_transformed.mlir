module {
  handshake.func @insertion_sort(%arg0: memref<30xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "n", "A_start", "start"], resNames = ["A_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:4 = lsq[%arg0 : memref<30xi32>] (%arg2, %13#0, %addressResult, %28#0, %addressResult_6, %42#0, %addressResult_20, %addressResult_22, %dataResult_23, %61#0, %addressResult_38, %dataResult_39, %result_46)  {groupSizes = [1 : i32, 1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %8 = mux %12#0 [%7, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i5>
    %11 = mux %12#1 [%trueResult_0, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %13:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %addressResult, %dataResult = load[%10] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i5>, <i32>, <i5>, <i32>
    %14 = br %9#1 {handshake.bb = 1 : ui32, handshake.name = "br1"} : <i32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %16 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %17 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br3"} : <i32>
    %18 = br %13#1 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <>
    %19 = mux %27#0 [%15#1, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %20:2 = fork [2] %19 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i32>
    %21 = trunci %20#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i5>
    %22 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = -1 : i5} : <>, <i5>
    %23 = mux %27#1 [%16, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %24 = mux %27#2 [%15#0, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %27#3 [%17, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %result_4, %index_5 = control_merge [%18, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %27:4 = fork [4] %index_5 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %28:2 = lazy_fork [2] %result_4 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %30 = addi %21, %22 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i5>
    %addressResult_6, %dataResult_7 = load[%30] %2#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load1"} : <i5>, <i32>, <i5>, <i32>
    %31 = cmpi sgt, %dataResult_7, %26#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %32:5 = fork [5] %31 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %32#4, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %32#3, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %32#2, %26#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %32#1, %20#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %33 = trunci %falseResult_15 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i32> to <i5>
    %trueResult_16, %falseResult_17 = cond_br %32#0, %28#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %34 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %35 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %36 = merge %trueResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %37 = merge %trueResult_14 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %38:3 = fork [3] %37 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %39 = trunci %38#0 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i32> to <i5>
    %40 = constant %46#0 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = -1 : i5} : <>, <i5>
    %41 = trunci %38#1 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i32> to <i5>
    %result_18, %index_19 = control_merge [%trueResult_16]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink2"} : <i1>
    %42:3 = lazy_fork [3] %result_18 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %43:2 = fork [2] %42#2 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <>
    %44 = constant %43#1 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %45 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %46:2 = fork [2] %45 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %47 = constant %46#1 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = -1 : i32} : <>, <i32>
    %48 = addi %39, %40 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i5>
    %addressResult_20, %dataResult_21 = load[%48] %2#2 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load2"} : <i5>, <i32>, <i5>, <i32>
    %addressResult_22, %dataResult_23 = store[%41] %dataResult_21 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store3"} : <i5>, <i32>, <i5>, <i32>
    %49 = addi %38#2, %47 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %50:2 = fork [2] %49 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i32>
    %51 = cmpi sgt, %50#1, %44 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %52:6 = fork [6] %51 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_24, %falseResult_25 = cond_br %52#5, %50#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    sink %falseResult_25 {handshake.name = "sink3"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %52#4, %34 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %52#3, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %52#2, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %52#1, %42#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %53 = constant %43#0 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = false} : <>, <i1>
    %trueResult_34, %falseResult_35 = cond_br %52#0, %53 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i1>
    sink %trueResult_34 {handshake.name = "sink4"} : <i1>
    %54 = extui %falseResult_35 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i1> to <i5>
    %55 = mux %60#0 [%33, %54] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %56 = mux %60#1 [%falseResult_9, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %57:2 = fork [2] %56 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i32>
    %58 = mux %60#2 [%falseResult_11, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %59 = mux %60#3 [%falseResult_13, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_36, %index_37 = control_merge [%falseResult_17, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %60:4 = fork [4] %index_37 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i1>
    %61:2 = lazy_fork [2] %result_36 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork3"} : <>
    %62 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %63 = constant %62 {handshake.bb = 4 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %addressResult_38, %dataResult_39 = store[%55] %59 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "store4"} : <i5>, <i32>, <i5>, <i32>
    %64 = addi %58, %63 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %65:2 = fork [2] %64 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i32>
    %66 = cmpi slt, %65#1, %57#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %67:3 = fork [3] %66 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %67#2, %65#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    sink %falseResult_41 {handshake.name = "sink5"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %67#1, %57#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    sink %falseResult_43 {handshake.name = "sink6"} : <i32>
    %trueResult_44, %falseResult_45 = cond_br %67#0, %61#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_3, %falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    sink %index_47 {handshake.name = "sink7"} : <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %2#3, %0#1 : <>, <>
  }
}

