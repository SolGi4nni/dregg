// Types for the pre-bundled @noble primitives (see noble-crypto.js).
export function keccak_256(data: Uint8Array): Uint8Array;
export function bytesToHex(bytes: Uint8Array): string;
export function hexToBytes(hex: string): Uint8Array;
export function concatBytes(...arrays: Uint8Array[]): Uint8Array;

export interface RecoveredSignature {
  r: bigint;
  s: bigint;
  recovery: number;
}

export interface RecoverablePoint {
  toRawBytes(compressed: boolean): Uint8Array;
}

export interface SignatureWithRecovery {
  recoverPublicKey(msgHash: Uint8Array): RecoverablePoint;
}

export interface SignatureClass {
  new (r: bigint, s: bigint): {
    addRecoveryBit(recovery: number): SignatureWithRecovery;
  };
}

export const secp256k1: {
  getPublicKey(privateKey: Uint8Array, isCompressed: boolean): Uint8Array;
  sign(msgHash: Uint8Array, privateKey: Uint8Array): RecoveredSignature;
  Signature: SignatureClass;
};
