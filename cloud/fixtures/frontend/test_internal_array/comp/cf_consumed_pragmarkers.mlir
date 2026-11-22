module {
  func.func @test_internal_array(%arg0: memref<640xi32> {handshake.arg_name = "A"}, %arg1: memref<640xi32> {handshake.arg_name = "B"}, %arg2: memref<640xi32> {handshake.arg_name = "C"}, %arg3: memref<640xi32> {handshake.arg_name = "result"}) {
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %alloca = memref.alloca() {handshake.name = "alloca0"} : memref<640xi32>
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant2"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb2
    %c32_i32 = arith.constant {handshake.name = "constant6"} 32 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c5_i64 = arith.constant {handshake.name = "constant8"} 5 : i64
    %5 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %6 = arith.shli %1, %c5_i64 {handshake.name = "shli0"} : i64
    %7 = arith.addi %6, %5 {handshake.name = "addi0"} : i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast0"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load0"} : memref<640xi32>
    %10 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    %11 = arith.shli %2, %c5_i64 {handshake.name = "shli1"} : i64
    %12 = arith.addi %11, %10 {handshake.name = "addi1"} : i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast1"} : i64 to index
    %14 = memref.load %arg1[%13] {handshake.name = "load1"} : memref<640xi32>
    %15 = arith.muli %9, %14 {handshake.name = "muli0"} : i32
    %16 = arith.extui %4 {handshake.name = "extui5"} : i32 to i64
    %17 = arith.shli %3, %c5_i64 {handshake.name = "shli2"} : i64
    %18 = arith.addi %17, %16 {handshake.name = "addi2"} : i64
    %19 = arith.index_cast %18 {handshake.name = "index_cast2"} : i64 to index
    memref.store %15, %alloca[%19] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<640xi32>
    %20 = arith.addi %4, %c1_i32 {handshake.name = "addi4"} : i32
    %21 = arith.cmpi ult, %20, %c32_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %21, ^bb2(%20 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c20_i32 = arith.constant {handshake.name = "constant9"} 20 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant10"} 0 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant11"} 1 : i32
    %22 = arith.addi %0, %c1_i32_2 {handshake.name = "addi5"} : i32
    %23 = arith.cmpi ult, %22, %c20_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %23, ^bb1(%22 : i32), ^bb4(%c0_i32_1 : i32) {handshake.name = "cond_br1"}
  ^bb4(%24: i32):  // 2 preds: ^bb3, ^bb6
    %c0_i32_3 = arith.constant {handshake.name = "constant12"} 0 : i32
    %25 = arith.extui %24 {handshake.name = "extui6"} : i32 to i64
    %26 = arith.extui %24 {handshake.name = "extui7"} : i32 to i64
    %27 = arith.extui %24 {handshake.name = "extui8"} : i32 to i64
    cf.br ^bb5(%c0_i32_3 : i32) {handshake.name = "br2"}
  ^bb5(%28: i32):  // 2 preds: ^bb4, ^bb5
    %c32_i32_4 = arith.constant {handshake.name = "constant13"} 32 : i32
    %c1_i32_5 = arith.constant {handshake.name = "constant14"} 1 : i32
    %c5_i64_6 = arith.constant {handshake.name = "constant15"} 5 : i64
    %29 = arith.extui %28 {handshake.name = "extui9"} : i32 to i64
    %30 = arith.shli %25, %c5_i64_6 {handshake.name = "shli3"} : i64
    %31 = arith.addi %30, %29 {handshake.name = "addi6"} : i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast3"} : i64 to index
    %33 = memref.load %alloca[%32] {handshake.name = "load3"} : memref<640xi32>
    %34 = arith.extui %28 {handshake.name = "extui10"} : i32 to i64
    %35 = arith.shli %26, %c5_i64_6 {handshake.name = "shli4"} : i64
    %36 = arith.addi %35, %34 {handshake.name = "addi8"} : i64
    %37 = arith.index_cast %36 {handshake.name = "index_cast4"} : i64 to index
    %38 = memref.load %arg2[%37] {handshake.name = "load4"} : memref<640xi32>
    %39 = arith.muli %33, %38 {handshake.name = "muli3"} : i32
    %40 = arith.extui %28 {handshake.name = "extui11"} : i32 to i64
    %41 = arith.shli %27, %c5_i64_6 {handshake.name = "shli5"} : i64
    %42 = arith.addi %41, %40 {handshake.name = "addi9"} : i64
    %43 = arith.index_cast %42 {handshake.name = "index_cast5"} : i64 to index
    memref.store %39, %arg3[%43] {handshake.name = "store5"} : memref<640xi32>
    %44 = arith.addi %28, %c1_i32_5 {handshake.name = "addi10"} : i32
    %45 = arith.cmpi ult, %44, %c32_i32_4 {handshake.name = "cmpi2"} : i32
    cf.cond_br %45, ^bb5(%44 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    %c20_i32_7 = arith.constant {handshake.name = "constant16"} 20 : i32
    %c1_i32_8 = arith.constant {handshake.name = "constant17"} 1 : i32
    %46 = arith.addi %24, %c1_i32_8 {handshake.name = "addi11"} : i32
    %47 = arith.cmpi ult, %46, %c20_i32_7 {handshake.name = "cmpi3"} : i32
    cf.cond_br %47, ^bb4(%46 : i32), ^bb7 {handshake.name = "cond_br3"}
  ^bb7:  // pred: ^bb6
    return {handshake.name = "return0"}
  }
}

