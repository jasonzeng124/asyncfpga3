module {
  handshake.func @jacobi_1d_imper(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "A_start", "B_start", "start"], resNames = ["A_end", "B_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg1 : memref<100xi32>] (%arg3, %20#0, %addressResult_6, %dataResult_7, %48#0, %addressResult_16, %68#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i7>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2:4 = lsq[%arg0 : memref<100xi32>] (%arg2, %20#2, %addressResult, %addressResult_2, %addressResult_4, %48#2, %addressResult_18, %dataResult_19, %68#0)  {groupSizes = [3 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %7 = mux %index [%5, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %result, %index = control_merge [%6, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <>
    %9 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = true} : <>, <i1>
    %10 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %11 = extui %10 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i1> to <i7>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i2>
    %13 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <>
    %14 = mux %19#1 [%11, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i7>, <i7>] to <i7>
    %15:5 = fork [5] %14 {handshake.bb = 2 : ui32, handshake.name = "fork2"} : <i7>
    %16 = extui %15#4 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i7> to <i8>
    %17 = constant %21#1 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i8} : <>, <i8>
    %18 = mux %19#0 [%12, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %result_0, %index_1 = control_merge [%13, %trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %19:2 = fork [2] %index_1 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i1>
    %20:4 = lazy_fork [4] %result_0 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork0"} : <>
    %21:4 = fork [4] %20#3 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %21#3 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %25 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = -1 : i7} : <>, <i7>
    %26 = addi %15#0, %25 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i7>
    %addressResult, %dataResult = load[%26] %2#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_2, %dataResult_3 = load[%15#3] %2#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i7>, <i32>, <i7>, <i32>
    %27 = addi %dataResult, %dataResult_3 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %28 = constant %21#0 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1 : i7} : <>, <i7>
    %29 = addi %15#1, %28 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i7>
    %addressResult_4, %dataResult_5 = load[%29] %2#2 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i7>, <i32>, <i7>, <i32>
    %30 = addi %27, %dataResult_5 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %31:2 = fork [2] %30 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %32 = shli %31#1, %24 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %33 = addi %31#0, %32 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i32>
    %addressResult_6, %dataResult_7 = store[%15#2] %33 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i7>, <i32>, <i7>, <i32>
    %34 = addi %16, %17 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i8>
    %35:2 = fork [2] %34 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i8>
    %36 = trunci %35#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %37 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 99 : i8} : <>, <i8>
    %38 = cmpi ult, %35#1, %37 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i8>
    %39:4 = fork [4] %38 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult, %falseResult = cond_br %39#0, %36 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_8, %falseResult_9 = cond_br %39#1, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i2>
    %trueResult_10, %falseResult_11 = cond_br %39#2, %20#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %40 = constant %21#2 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = true} : <>, <i1>
    %trueResult_12, %falseResult_13 = cond_br %39#3, %40 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i1>
    sink %trueResult_12 {handshake.name = "sink1"} : <i1>
    %41 = extui %falseResult_13 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i1> to <i7>
    %42 = mux %47#1 [%41, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i7>, <i7>] to <i7>
    %43:3 = fork [3] %42 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i7>
    %44 = extui %43#2 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i7> to <i8>
    %45 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i8} : <>, <i8>
    %46 = mux %47#0 [%falseResult_9, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i2>, <i2>] to <i2>
    %result_14, %index_15 = control_merge [%falseResult_11, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %47:2 = fork [2] %index_15 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %48:3 = lazy_fork [3] %result_14 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork1"} : <>
    %49 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %addressResult_16, %dataResult_17 = load[%43#1] %1#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load4"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_18, %dataResult_19 = store[%43#0] %dataResult_17 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : <i7>, <i32>, <i7>, <i32>
    %51 = addi %44, %45 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i8>
    %52:2 = fork [2] %51 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i8>
    %53 = trunci %52#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i8> to <i7>
    %54 = constant %49 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 99 : i8} : <>, <i8>
    %55 = cmpi ult, %52#1, %54 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i8>
    %56:3 = fork [3] %55 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_20, %falseResult_21 = cond_br %56#0, %53 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i7>
    sink %falseResult_21 {handshake.name = "sink2"} : <i7>
    %trueResult_22, %falseResult_23 = cond_br %56#1, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i2>
    %trueResult_24, %falseResult_25 = cond_br %56#2, %48#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %57 = merge %falseResult_23 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i2>
    %58 = extui %57 {handshake.bb = 4 : ui32, handshake.name = "extui10"} : <i2> to <i3>
    %59 = constant %61 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 1 : i3} : <>, <i3>
    %result_26, %index_27 = control_merge [%falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_27 {handshake.name = "sink3"} : <i1>
    %60 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %61 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %62 = addi %58, %59 {handshake.bb = 4 : ui32, handshake.name = "addi6"} : <i3>
    %63:2 = fork [2] %62 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i3>
    %64 = trunci %63#0 {handshake.bb = 4 : ui32, handshake.name = "trunci2"} : <i3> to <i2>
    %65 = constant %60 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 3 : i3} : <>, <i3>
    %66 = cmpi ult, %63#1, %65 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i3>
    %67:2 = fork [2] %66 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_28, %falseResult_29 = cond_br %67#0, %64 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i2>
    sink %falseResult_29 {handshake.name = "sink4"} : <i2>
    %trueResult_30, %falseResult_31 = cond_br %67#1, %result_26 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_32, %index_33 = control_merge [%falseResult_31]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_33 {handshake.name = "sink5"} : <i1>
    %68:2 = fork [2] %result_32 {handshake.bb = 5 : ui32, handshake.name = "fork14"} : <>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %2#3, %1#1, %0#1 : <>, <>, <>
  }
}

