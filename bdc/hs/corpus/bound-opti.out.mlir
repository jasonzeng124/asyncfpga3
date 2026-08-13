module {
  handshake.func @boundEqCst(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i6>
    %1 = constant %arg1 {handshake.name = "constant0", value = 16 : i32} : <>, <i32>
    %2 = cmpi eq, %arg0, %1 {handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.name = "cond_br0"} : <i1>, <i6>
    %3 = extsi %trueResult {handshake.name = "extsi0"} : <i6> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @boundUleCst(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i6>
    %1 = constant %arg1 {handshake.name = "constant0", value = 16 : i32} : <>, <i32>
    %2 = cmpi ule, %arg0, %1 {handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.name = "cond_br0"} : <i1>, <i6>
    %3 = extui %trueResult {handshake.name = "extui0"} : <i6> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @boundUleCstFlip(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i6>
    %1 = constant %arg1 {handshake.name = "constant0", value = 16 : i32} : <>, <i32>
    %2 = cmpi ule, %1, %arg0 {handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.name = "cond_br0"} : <i1>, <i6>
    %3 = extui %falseResult {handshake.name = "extui0"} : <i6> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @boundUleNegative(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %1 = cmpi ule, %0, %arg0 {handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %arg0 {handshake.name = "cond_br0"} : <i1>, <i32>
    end {handshake.name = "end0"} %falseResult : <i32>
  }
}


// -----
module {
  handshake.func @argUleArg(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i8>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "bound", "start"], resNames = ["out0"]} {
    %0 = extsi %arg1 {handshake.name = "extsi0"} : <i8> to <i32>
    %1 = cmpi ule, %arg0, %0 {handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %arg0 {handshake.name = "cond_br0"} : <i1>, <i32>
    end {handshake.name = "end0"} %trueResult : <i32>
  }
}


// -----
module {
  handshake.func @mulCmps(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i4>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "bound", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %1 = constant %arg2 {handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.name = "constant1", value = 50 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.name = "constant2", value = 100 : i32} : <>, <i32>
    %4 = extsi %arg1 {handshake.name = "extsi0"} : <i4> to <i32>
    %5 = cmpi uge, %arg0, %1 {handshake.name = "cmpi0"} : <i32>
    %6 = cmpi ult, %arg0, %3 {handshake.name = "cmpi1"} : <i32>
    %7 = cmpi ne, %arg0, %2 {handshake.name = "cmpi2"} : <i32>
    %8 = cmpi ult, %arg0, %4 {handshake.name = "cmpi3"} : <i32>
    %9 = andi %5, %6 {handshake.name = "andi0"} : <i1>
    %10 = andi %7, %8 {handshake.name = "andi1"} : <i1>
    %11 = andi %9, %10 {handshake.name = "andi2"} : <i1>
    %trueResult, %falseResult = cond_br %11, %0 {handshake.name = "cond_br0"} : <i1>, <i7>
    %12 = extui %trueResult {handshake.name = "extui0"} : <i7> to <i32>
    end {handshake.name = "end0"} %12 : <i32>
  }
}


// -----
module {
  handshake.func @simpleLoop(%arg0: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = source {handshake.name = "source0"} : <>
    %1 = constant %arg0 {handshake.name = "constant0", value = 0 : i4} : <>, <i4>
    %2 = merge %1, %9 {handshake.name = "merge0"} : <i4>
    %3 = extui %2 {handshake.name = "extui0"} : <i4> to <i5>
    %4 = constant %0 {handshake.name = "constant1", value = 1 : i5} : <>, <i5>
    %5 = addi %3, %4 {handshake.name = "addi0"} : <i5>
    %6 = constant %0 {handshake.name = "constant2", value = -16 : i5} : <>, <i5>
    %7 = cmpi ult, %5, %6 {handshake.name = "cmpi0"} : <i5>
    %trueResult, %falseResult = cond_br %7, %5 {handshake.name = "cond_br0"} : <i1>, <i5>
    %8 = extui %falseResult {handshake.name = "extui1"} : <i5> to <i32>
    %9 = trunci %trueResult {handshake.name = "trunci0"} : <i5> to <i4>
    end {handshake.name = "end0"} %8 : <i32>
  }
}


// -----
module {
  handshake.func @nestedLoop(%arg0: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %result, %index = control_merge [%arg0, %falseResult_11]  {handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %2 = mux %index [%1, %falseResult_9] {handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = constant %0 {handshake.name = "constant1", value = 0 : i4} : <>, <i4>
    %4 = mux %index [%3, %trueResult] {handshake.name = "mux0"} : <i1>, [<i4>, <i4>] to <i4>
    %5 = extui %4 {handshake.name = "extui0"} : <i4> to <i5>
    %6 = constant %0 {handshake.name = "constant2", value = 1 : i5} : <>, <i5>
    %7 = addi %5, %6 {handshake.name = "addi1"} : <i5>
    %8 = trunci %7 {handshake.name = "trunci0"} : <i5> to <i4>
    %9 = constant %0 {handshake.name = "constant3", value = -16 : i5} : <>, <i5>
    %10 = cmpi ult, %7, %9 {handshake.name = "cmpi1"} : <i5>
    %trueResult, %falseResult = cond_br %10, %8 {handshake.name = "cond_br1"} : <i1>, <i4>
    %trueResult_0, %falseResult_1 = cond_br %10, %2 {handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %10, %result {handshake.name = "cond_br3"} : <i1>, <>
    %11 = source {handshake.name = "source1"} : <>
    %result_4, %index_5 = control_merge [%trueResult_2, %26]  {handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %12 = mux %index_5 [%trueResult_0, %25] {handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = constant %11 {handshake.name = "constant4", value = 0 : i5} : <>, <i5>
    %14 = mux %index_5 [%13, %trueResult_6] {handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %15 = extui %14 {handshake.name = "extui1"} : <i5> to <i6>
    %16 = constant %11 {handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %17 = addi %15, %16 {handshake.name = "addi0"} : <i6>
    %18 = trunci %17 {handshake.name = "trunci1"} : <i6> to <i5>
    %19 = constant %11 {handshake.name = "constant6", value = -32 : i6} : <>, <i6>
    %20 = cmpi ult, %17, %19 {handshake.name = "cmpi0"} : <i6>
    %trueResult_6, %falseResult_7 = cond_br %20, %18 {handshake.name = "cond_br0"} : <i1>, <i5>
    %trueResult_8, %falseResult_9 = cond_br %20, %12 {handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %20, %result_4 {handshake.name = "cond_br5"} : <i1>, <>
    %21 = source {handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.name = "constant7", value = 10 : i32} : <>, <i32>
    %result_12, %index_13 = control_merge [%trueResult_10]  {handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %23 = merge %trueResult_8 {handshake.name = "merge0"} : <i32>
    %24 = addi %23, %22 {handshake.name = "addi2"} : <i32>
    %25 = br %24 {handshake.name = "br0"} : <i32>
    %26 = br %result_12 {handshake.name = "br1"} : <>
    %27 = merge %falseResult_1 {handshake.name = "merge1"} : <i32>
    end {handshake.name = "end0"} %27 : <i32>
  }
}


// -----
module {
  handshake.func @boundConj(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i1>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i1> attributes {argNames = ["arg0", "arg2", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.name = "extui0"} : <i1> to <i32>
    %1 = cmpi ne, %0, %arg0 {handshake.name = "cmpi0"} : <i32>
    %2 = cmpi ne, %0, %arg2 {handshake.name = "cmpi1"} : <i32>
    %3 = andi %1, %2 {handshake.name = "andi0"} : <i1>
    %trueResult, %falseResult = cond_br %3, %arg0 {handshake.name = "cond_br0"} : <i1>, <i32>
    %4 = cmpi ne, %0, %falseResult {handshake.name = "cmpi2"} : <i32>
    end {handshake.name = "end0"} %4 : <i1>
  }
}


// -----
module {
  handshake.func @test32(%arg0: !handshake.channel<i16>, %arg1: !handshake.channel<i8>, %arg2: memref<32xi16>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["arg0", "arg2", "arg3", "arg6"], resNames = ["out0", "out1", "out2", "out3"]} {
    %0:2 = lsq[%arg2 : memref<32xi16>] (%arg3, %result, %addressResult, %dataResult, %result_12, %addressResult_14, %falseResult_19)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i16>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<i16>, !handshake.control<>)
    %1 = source {handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.name = "constant0", value = 0 : i8} : <>, <i8>
    %3 = cmpi eq, %arg1, %2 {handshake.name = "cmpi1"} : <i8>
    %trueResult, %falseResult = cond_br %3, %arg0 {handshake.name = "cond_br1"} : <i1>, <i16>
    %trueResult_0, %falseResult_1 = cond_br %3, %arg3 {handshake.name = "cond_br2"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %3, %3 {handshake.name = "cond_br3"} : <i1>, <i1>
    %4 = mux %index [%falseResult, %falseResult_5] {handshake.name = "mux1"} : <i1>, [<i16>, <i16>] to <i16>
    %5 = mux %index [%falseResult_3, %falseResult_9] {handshake.name = "mux2"} : <i1>, [<i1>, <i1>] to <i1>
    %result, %index = control_merge [%falseResult_1, %falseResult_7]  {handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.name = "constant1", value = 0 : i16} : <>, <i16>
    %7 = constant %result {handshake.name = "constant2", value = 0 : i5} : <>, <i5>
    %addressResult, %dataResult = store[%7] %6 {handshake.name = "store0"} : <i5>, <i16>, <i5>, <i16>
    %trueResult_4, %falseResult_5 = cond_br %5, %4 {handshake.name = "cond_br4"} : <i1>, <i16>
    %trueResult_6, %falseResult_7 = cond_br %5, %result {handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %5, %5 {handshake.name = "cond_br6"} : <i1>, <i1>
    %result_10, %index_11 = control_merge [%trueResult_0, %trueResult_6]  {handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %8 = mux %index_13 [%4, %trueResult_16] {handshake.name = "mux0"} : <i1>, [<i16>, <i16>] to <i16>
    %9 = extui %8 {handshake.name = "extui0"} : <i16> to <i17>
    %result_12, %index_13 = control_merge [%result_10, %trueResult_18]  {handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %10 = source {handshake.name = "source1"} : <>
    %11 = constant %result_12 {handshake.name = "constant3", value = 0 : i5} : <>, <i5>
    %addressResult_14, %dataResult_15 = load[%11] %0#0 {handshake.name = "load0"} : <i5>, <i16>, <i5>, <i16>
    %12 = extsi %dataResult_15 {handshake.name = "extsi0"} : <i16> to <i17>
    %13 = xori %9, %12 {handshake.name = "xori0"} : <i17>
    %14 = constant %10 {handshake.name = "constant4", value = 0 : i17} : <>, <i17>
    %15 = cmpi eq, %13, %14 {handshake.name = "cmpi0"} : <i17>
    %trueResult_16, %falseResult_17 = cond_br %15, %8 {handshake.name = "cond_br0"} : <i1>, <i16>
    %trueResult_18, %falseResult_19 = cond_br %15, %result_12 {handshake.name = "cond_br7"} : <i1>, <>
    end {handshake.name = "end0"} %1, %arg3, %arg3, %arg3 : <>, <>, <>, <>
  }
}

