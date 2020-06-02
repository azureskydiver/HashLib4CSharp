/*
HashLib4CSharp Library
Copyright (c) 2020 Ugochukwu Mmaduekwe
GitHub Profile URL <https://github.com/Xor-el>

Distributed under the MIT software license, see the accompanying LICENSE file
or visit http://www.opensource.org/licenses/mit-license.php.

Acknowledgements:
This library was sponsored by Sphere 10 Software (https://www.sphere10.com)
for the purposes of supporting the XXX (https://YYY) project.
*/

using System;
using System.Diagnostics;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using HashLib4CSharp.Base;
using HashLib4CSharp.Enum;
using HashLib4CSharp.Interfaces;
using HashLib4CSharp.Utils;

namespace HashLib4CSharp.Crypto
{
    internal class Blake3 : Hash, ICryptoNotBuiltIn, ITransformBlock
    {
        private const string MaximumOutputLengthExceeded = "Maximum output length is 2^64 bytes";
        private const string InvalidKeyLength = "Key length Must not be greater than {0}, '{1}'";

        private const int ChunkSize = 1024;
        private const int BlockSizeInBytes = 64;

        private const uint flagChunkStart = 1 << 0;
        private const uint flagChunkEnd = 1 << 1;
        private const uint flagParent = 1 << 2;
        private const uint flagRoot = 1 << 3;
        private const uint flagKeyedHash = 1 << 4;

        // maximum size in bytes this digest output reader can produce
        private const ulong MaxDigestLengthInBytes = ulong.MaxValue;

        internal const int KeyLengthInBytes = 32;

        internal static readonly uint[] IV =
        {
            0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
            0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
        };

        protected Blake3ChunkState ChunkState;
        protected Blake3OutputReader OutputReader;
        protected uint[] Key;
        protected uint Flags;

        // log(n) set of Merkle subtree roots, at most one per height.
        // stack [54][8]uint32
        protected uint[][] Stack; // 2^54 * chunkSize = 2^64

        // bit vector indicating which stack elems are valid; also number of chunks added
        protected ulong Used;

        protected static class Blake3Compressor
        {
            public static uint[] ComputeChainingValue(ReadOnlySpan<uint> cv,
                                                      ReadOnlySpan<uint> block,
                                                      uint flags,
                                                      uint blockLen,
                                                      ulong counter = 0)
            {
                return Compress(cv: cv,
                                block: block,
                                flags: flags,
                                blockLen: blockLen,
                                counter: counter)
                        .Take(8)
                        .ToArray();
            }

            // compress is the core hash function, generating 16 pseudorandom words from a
            // node.
            // NOTE: we unroll all of the rounds, as well as the permutations that occur
            // between rounds.
            public static uint [] Compress(ReadOnlySpan<uint> cv,
                                           ReadOnlySpan<uint> block,
                                           uint flags,
                                           uint blockLen,
                                           ulong counter)
            {
                // initializes state here
                var state = new uint[16];

                state[0] = cv[0];
                state[1] = cv[1];
                state[2] = cv[2];
                state[3] = cv[3];
                state[4] = cv[4];
                state[5] = cv[5];
                state[6] = cv[6];
                state[7] = cv[7];
                state[8] = Blake3.IV[0];
                state[9] = Blake3.IV[1];
                state[10] = Blake3.IV[2];
                state[11] = Blake3.IV[3];
                state[12] = (uint)counter;
                state[13] = (uint)(counter >> 32);
                state[14] = blockLen;
                state[15] = flags;

                // NOTE: we unroll all of the rounds, as well as the permutations that occur
                // between rounds.
                // Round 0
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[0], block[1]);
                G(state, 1, 5, 9, 13, block[2], block[3]);
                G(state, 2, 6, 10, 14, block[4], block[5]);
                G(state, 3, 7, 11, 15, block[6], block[7]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[8], block[9]);
                G(state, 1, 6, 11, 12, block[10], block[11]);
                G(state, 2, 7, 8, 13, block[12], block[13]);
                G(state, 3, 4, 9, 14, block[14], block[15]);

                // Round 1
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[2], block[6]);
                G(state, 1, 5, 9, 13, block[3], block[10]);
                G(state, 2, 6, 10, 14, block[7], block[0]);
                G(state, 3, 7, 11, 15, block[4], block[13]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[1], block[11]);
                G(state, 1, 6, 11, 12, block[12], block[5]);
                G(state, 2, 7, 8, 13, block[9], block[14]);
                G(state, 3, 4, 9, 14, block[15], block[8]);

                // Round 2
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[3], block[4]);
                G(state, 1, 5, 9, 13, block[10], block[12]);
                G(state, 2, 6, 10, 14, block[13], block[2]);
                G(state, 3, 7, 11, 15, block[7], block[14]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[6], block[5]);
                G(state, 1, 6, 11, 12, block[9], block[0]);
                G(state, 2, 7, 8, 13, block[11], block[15]);
                G(state, 3, 4, 9, 14, block[8], block[1]);

                // Round 3
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[10], block[7]);
                G(state, 1, 5, 9, 13, block[12], block[9]);
                G(state, 2, 6, 10, 14, block[14], block[3]);
                G(state, 3, 7, 11, 15, block[13], block[15]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[4], block[0]);
                G(state, 1, 6, 11, 12, block[11], block[2]);
                G(state, 2, 7, 8, 13, block[5], block[8]);
                G(state, 3, 4, 9, 14, block[1], block[6]);

                // Round 4
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[12], block[13]);
                G(state, 1, 5, 9, 13, block[9], block[11]);
                G(state, 2, 6, 10, 14, block[15], block[10]);
                G(state, 3, 7, 11, 15, block[14], block[8]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[7], block[2]);
                G(state, 1, 6, 11, 12, block[5], block[3]);
                G(state, 2, 7, 8, 13, block[0], block[1]);
                G(state, 3, 4, 9, 14, block[6], block[4]);

                // Round 5
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[9], block[14]);
                G(state, 1, 5, 9, 13, block[11], block[5]);
                G(state, 2, 6, 10, 14, block[8], block[12]);
                G(state, 3, 7, 11, 15, block[15], block[1]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[13], block[3]);
                G(state, 1, 6, 11, 12, block[0], block[10]);
                G(state, 2, 7, 8, 13, block[2], block[6]);
                G(state, 3, 4, 9, 14, block[4], block[7]);

                // Round 6
                // Mix the columns.
                G(state, 0, 4, 8, 12, block[11], block[15]);
                G(state, 1, 5, 9, 13, block[5], block[0]);
                G(state, 2, 6, 10, 14, block[1], block[9]);
                G(state, 3, 7, 11, 15, block[8], block[6]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, block[14], block[10]);
                G(state, 1, 6, 11, 12, block[2], block[12]);
                G(state, 2, 7, 8, 13, block[3], block[4]);
                G(state, 3, 4, 9, 14, block[7], block[13]);

                // compression finalization

                state[0] = state[0] ^ state[8];
                state[1] = state[1] ^ state[9];
                state[2] = state[2] ^ state[10];
                state[3] = state[3] ^ state[11];
                state[4] = state[4] ^ state[12];
                state[5] = state[5] ^ state[13];
                state[6] = state[6] ^ state[14];
                state[7] = state[7] ^ state[15];
                state[8] = state[8] ^ cv[0];
                state[9] = state[9] ^ cv[1];
                state[10] = state[10] ^ cv[2];
                state[11] = state[11] ^ cv[3];
                state[12] = state[12] ^ cv[4];
                state[13] = state[13] ^ cv[5];
                state[14] = state[14] ^ cv[6];
                state[15] = state[15] ^ cv[7];

                return state;
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            private static void G(Span<uint> state, int a, int b, int c, int d, uint x, uint y)
            {
                var aa = state[a];
                var bb = state[b];
                var cc = state[c];
                var dd = state[d];

                unchecked
                {
                    aa = aa + bb + x;
                    dd = Bits.RotateRight32(dd ^ aa, 16);
                    cc += dd;
                    bb = Bits.RotateRight32(bb ^ cc, 12);
                    aa = aa + bb + y;
                    dd = Bits.RotateRight32(dd ^ aa, 8);
                    cc += dd;
                    bb = Bits.RotateRight32(bb ^ cc, 7);
                }

                state[a] = aa;
                state[b] = bb;
                state[c] = cc;
                state[d] = dd;
            }
        }

        // A Blake3Node represents a chunk or parent in the BLAKE3 Merkle tree. In BLAKE3
        // terminology, the elements of the bottom layer (aka "leaves") of the tree are
        // called chunk nodes, and the elements of upper layers (aka "interior nodes")
        // are called parent nodes.
        //
        // Computing a BLAKE3 hash involves splitting the input into chunk nodes, then
        // repeatedly merging these nodes into parent nodes, until only a single "root"
        // node remains. The root node can then be used to generate up to 2^64 - 1 bytes
        // of pseudorandom output.
        protected sealed class Blake3Node
        {
            // the chaining value from the previous state
            public uint[] CV;

            // the current state
            public uint[] Block;
            public ulong Counter;
            public uint BlockLen, Flags;


            private Blake3Node()
            {
                CV = new uint[8];
                Block = new uint[16];
                Counter = 0;
                BlockLen = 0;
                Flags = 0;
            }

            public Blake3Node Clone() =>
                new Blake3Node
                {
                    CV = ArrayUtils.Clone(CV),
                    Block = ArrayUtils.Clone(Block),
                    Counter = Counter,
                    BlockLen = BlockLen,
                    Flags = Flags
                };

            // ChainingValue returns the first 8 words of the compressed node. This is used
            // in two places. First, when a chunk node is being constructed, its cv is
            // overwritten with this value after each block of input is processed. Second,
            // when two nodes are merged into a parent, each of their chaining values
            // supplies half of the new node's block.
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public unsafe void ChainingValue(uint* result)
            {
                var full = new uint[16];
                fixed (uint* ptrFull = full)
                {
                    Compress(ptrFull);
                    PointerUtils.MemMove(&result[0], ptrFull, 8 * sizeof(uint));
                }
            }

            // compress is the core hash function, generating 16 pseudorandom words from a
            // node.
            // NOTE: we unroll all of the rounds, as well as the permutations that occur
            // between rounds.
            public unsafe void Compress(uint* state)
            {
                // initializes state here
                state[0] = CV[0];
                state[1] = CV[1];
                state[2] = CV[2];
                state[3] = CV[3];
                state[4] = CV[4];
                state[5] = CV[5];
                state[6] = CV[6];
                state[7] = CV[7];
                state[8] = IV[0];
                state[9] = IV[1];
                state[10] = IV[2];
                state[11] = IV[3];
                state[12] = (uint) Counter;
                state[13] = (uint) (Counter >> 32);
                state[14] = BlockLen;
                state[15] = Flags;

                // NOTE: we unroll all of the rounds, as well as the permutations that occur
                // between rounds.
                // Round 0
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[0], Block[1]);
                G(state, 1, 5, 9, 13, Block[2], Block[3]);
                G(state, 2, 6, 10, 14, Block[4], Block[5]);
                G(state, 3, 7, 11, 15, Block[6], Block[7]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[8], Block[9]);
                G(state, 1, 6, 11, 12, Block[10], Block[11]);
                G(state, 2, 7, 8, 13, Block[12], Block[13]);
                G(state, 3, 4, 9, 14, Block[14], Block[15]);

                // Round 1
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[2], Block[6]);
                G(state, 1, 5, 9, 13, Block[3], Block[10]);
                G(state, 2, 6, 10, 14, Block[7], Block[0]);
                G(state, 3, 7, 11, 15, Block[4], Block[13]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[1], Block[11]);
                G(state, 1, 6, 11, 12, Block[12], Block[5]);
                G(state, 2, 7, 8, 13, Block[9], Block[14]);
                G(state, 3, 4, 9, 14, Block[15], Block[8]);

                // Round 2
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[3], Block[4]);
                G(state, 1, 5, 9, 13, Block[10], Block[12]);
                G(state, 2, 6, 10, 14, Block[13], Block[2]);
                G(state, 3, 7, 11, 15, Block[7], Block[14]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[6], Block[5]);
                G(state, 1, 6, 11, 12, Block[9], Block[0]);
                G(state, 2, 7, 8, 13, Block[11], Block[15]);
                G(state, 3, 4, 9, 14, Block[8], Block[1]);

                // Round 3
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[10], Block[7]);
                G(state, 1, 5, 9, 13, Block[12], Block[9]);
                G(state, 2, 6, 10, 14, Block[14], Block[3]);
                G(state, 3, 7, 11, 15, Block[13], Block[15]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[4], Block[0]);
                G(state, 1, 6, 11, 12, Block[11], Block[2]);
                G(state, 2, 7, 8, 13, Block[5], Block[8]);
                G(state, 3, 4, 9, 14, Block[1], Block[6]);

                // Round 4
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[12], Block[13]);
                G(state, 1, 5, 9, 13, Block[9], Block[11]);
                G(state, 2, 6, 10, 14, Block[15], Block[10]);
                G(state, 3, 7, 11, 15, Block[14], Block[8]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[7], Block[2]);
                G(state, 1, 6, 11, 12, Block[5], Block[3]);
                G(state, 2, 7, 8, 13, Block[0], Block[1]);
                G(state, 3, 4, 9, 14, Block[6], Block[4]);

                // Round 5
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[9], Block[14]);
                G(state, 1, 5, 9, 13, Block[11], Block[5]);
                G(state, 2, 6, 10, 14, Block[8], Block[12]);
                G(state, 3, 7, 11, 15, Block[15], Block[1]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[13], Block[3]);
                G(state, 1, 6, 11, 12, Block[0], Block[10]);
                G(state, 2, 7, 8, 13, Block[2], Block[6]);
                G(state, 3, 4, 9, 14, Block[4], Block[7]);

                // Round 6
                // Mix the columns.
                G(state, 0, 4, 8, 12, Block[11], Block[15]);
                G(state, 1, 5, 9, 13, Block[5], Block[0]);
                G(state, 2, 6, 10, 14, Block[1], Block[9]);
                G(state, 3, 7, 11, 15, Block[8], Block[6]);

                // Mix the rows.
                G(state, 0, 5, 10, 15, Block[14], Block[10]);
                G(state, 1, 6, 11, 12, Block[2], Block[12]);
                G(state, 2, 7, 8, 13, Block[3], Block[4]);
                G(state, 3, 4, 9, 14, Block[7], Block[13]);

                // compression finalization

                state[0] = state[0] ^ state[8];
                state[1] = state[1] ^ state[9];
                state[2] = state[2] ^ state[10];
                state[3] = state[3] ^ state[11];
                state[4] = state[4] ^ state[12];
                state[5] = state[5] ^ state[13];
                state[6] = state[6] ^ state[14];
                state[7] = state[7] ^ state[15];
                state[8] = state[8] ^ CV[0];
                state[9] = state[9] ^ CV[1];
                state[10] = state[10] ^ CV[2];
                state[11] = state[11] ^ CV[3];
                state[12] = state[12] ^ CV[4];
                state[13] = state[13] ^ CV[5];
                state[14] = state[14] ^ CV[6];
                state[15] = state[15] ^ CV[7];
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            private static unsafe void G(uint* state, uint a, uint b, uint c, uint d, uint x, uint y)
            {
                var aa = state[a];
                var bb = state[b];
                var cc = state[c];
                var dd = state[d];

                aa = aa + bb + x;
                dd = Bits.RotateRight32(dd ^ aa, 16);
                cc += dd;
                bb = Bits.RotateRight32(bb ^ cc, 12);
                aa = aa + bb + y;
                dd = Bits.RotateRight32(dd ^ aa, 8);
                cc += dd;
                bb = Bits.RotateRight32(bb ^ cc, 7);

                state[a] = aa;
                state[b] = bb;
                state[c] = cc;
                state[d] = dd;
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            private static Blake3Node CreateBlake3Node(uint[] cv, uint[] block,
                ulong counter, uint blockLen, uint flags) =>
                new Blake3Node
                {
                    CV = ArrayUtils.Clone(cv),
                    Block = ArrayUtils.Clone(block),
                    Counter = counter,
                    BlockLen = blockLen,
                    Flags = flags
                };

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public static Blake3Node ParentNode(uint[] left, uint[] right, uint[] key, uint flags) =>
                CreateBlake3Node(key, ArrayUtils.Concatenate(left, right), 0, BlockSizeInBytes, flags | flagParent);

            public static Blake3Node DefaultBlake3Node() => new Blake3Node();
        }

        // Blake3ChunkState manages the state involved in hashing a single chunk of input.
        protected sealed class Blake3ChunkState
        {
            private Blake3Node _n;
            private byte[] _block;
            private int _blockLen;
            public int BytesConsumed;

            private Blake3ChunkState()
            {
                _n = Blake3Node.DefaultBlake3Node();
                _block = new byte[BlockSizeInBytes];
                _blockLen = 0;
                BytesConsumed = 0;
            }

            public Blake3ChunkState Clone() =>
                new Blake3ChunkState
                {
                    _n = _n.Clone(), _block = ArrayUtils.Clone(_block), _blockLen = _blockLen,
                    BytesConsumed = BytesConsumed
                };

            // ChunkCounter is the index of this chunk, i.e. the number of chunks that have
            // been processed prior to this one.
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public ulong ChunkCounter() => _n.Counter;

            public bool IsComplete => BytesConsumed == ChunkSize;

            public uint[] ComputeChunkEndChainingValue()
            {
                for (int i = _blockLen; i < BlockSizeInBytes; i++)
                    _block[i] = 0;

                return Blake3Compressor.ComputeChainingValue(cv: _n.CV,
                                                             block: MemoryMarshal.Cast<byte, uint>(_block),
                                                             flags: _n.Flags | flagChunkEnd,
                                                             blockLen: (uint) _blockLen,
                                                             counter: _n.Counter);
            }

            // node returns a node containing the chunkState's current state, with the
            // ChunkEnd flag set.
            public unsafe Blake3Node Node()
            {
                var result = _n.Clone();

                fixed (byte* blockPtr = _block)
                {
                    fixed (uint* resultPtr = result.Block)
                    {
                        // pad the remaining space in the block with zeros
                        PointerUtils.MemSet(blockPtr + _blockLen, 0, _block.Length - _blockLen);
                        Converters.le32_copy(blockPtr, 0, resultPtr, 0, BlockSizeInBytes);
                    }
                }

                result.BlockLen = (uint) _blockLen;
                result.Flags |= flagChunkEnd;

                return result;
            }

            // update incorporates input into the chunkState.
            public void Update(ReadOnlySpan<byte> data)
            {
                var blockSpan = _block.AsSpan();
                var blockSpanAsUint = MemoryMarshal.Cast<byte, uint>(blockSpan);

                while (!data.IsEmpty)
                {
                    // If the block buffer is full, compress it and clear it. More
                    // input is coming, so this compression is not flagChunkEnd.
                    if (_blockLen == BlockSizeInBytes)
                    {
                        _n.CV = Blake3Compressor.ComputeChainingValue(
                                    cv: _n.CV,
                                    block: blockSpanAsUint,
                                    counter: _n.Counter,
                                    blockLen: _n.BlockLen,
                                    flags: _n.Flags);

                        // clear the start flag for all but the first block
                        _n.Flags &= _n.Flags ^ flagChunkStart;
                        _blockLen = 0;
                    }

                    // Copy input bytes into the chunk block.
                    //$ TODO: Handle blockSpanAsUint running on big endian
                    var count = Math.Min(BlockSizeInBytes - _blockLen, data.Length);
                    data.Slice(0, count).CopyTo(blockSpan.Slice(_blockLen));

                    _blockLen += count;
                    BytesConsumed += count;
                    data = data.Slice(count);
                }
            }

            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            public static Blake3ChunkState CreateBlake3ChunkState(uint[] iv, ulong chunkCounter, uint flags) =>
                new Blake3ChunkState
                {
                    _n =
                    {
                        CV = ArrayUtils.Clone(iv),
                        Counter = chunkCounter,
                        BlockLen = BlockSizeInBytes,
                        // compress the first block with the start flag set
                        Flags = flags | flagChunkStart
                    }
                };
        }

        protected sealed class Blake3OutputReader
        {
            private byte[] _block;
            public Blake3Node N;
            public ulong Offset;

            private Blake3OutputReader()
            {
                N = Blake3Node.DefaultBlake3Node();
                _block = new byte[BlockSizeInBytes];
                Offset = 0;
            }

            public Blake3OutputReader Clone() =>
                new Blake3OutputReader
                {
                    N = N.Clone(), _block = ArrayUtils.Clone(_block), Offset = Offset
                };

            public unsafe void Read(byte[] dest, ulong destOffset, ulong outputLength)
            {
                var words = new uint[16];

                if (Offset == MaxDigestLengthInBytes)
                    throw new ArgumentException(MaximumOutputLengthExceeded);
                var remainder = MaxDigestLengthInBytes - Offset;
                outputLength = Math.Min(outputLength, remainder);

                fixed (uint* wordsPtr = words)
                {
                    fixed (byte* blockPtr = _block, destPtr = dest)
                    {
                        while (outputLength > 0)
                        {
                            if ((Offset & (BlockSizeInBytes - 1)) == 0)
                            {
                                N.Counter = Offset / BlockSizeInBytes;
                                N.Compress(wordsPtr);
                                Converters.le32_copy(wordsPtr, 0, blockPtr, 0, BlockSizeInBytes);
                            }

                            var blockOffset = Offset & (BlockSizeInBytes - 1);

                            var diff = (ulong) _block.Length - blockOffset;

                            var count = (int) Math.Min(outputLength, diff);

                            PointerUtils.MemMove(destPtr + destOffset, blockPtr + blockOffset, count);

                            outputLength -= (ulong) count;
                            destOffset += (ulong) count;
                            Offset += (ulong) count;
                        }
                    }
                }
            }

            public static Blake3OutputReader DefaultBlake3OutputReader() => new Blake3OutputReader();
        }

        private unsafe Blake3Node RootNode()
        {
            var result = ChunkState.Node();
            var temp = new uint[8];

            var trailingZeros64 = TrailingZeros64(Used);
            var len64 = Len64(Used);

            fixed (uint* ptrTemp = temp)
            {
                int idx;
                for (idx = trailingZeros64; idx < len64; idx++)
                {
                    if (!HasSubTreeAtHeight(idx)) continue;
                    result.ChainingValue(ptrTemp);
                    result = Blake3Node.ParentNode(Stack[idx], temp, Key, Flags);
                }
            }

            result.Flags |= flagRoot;

            return result;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private bool HasSubTreeAtHeight(int idx) => (Used & ((uint) 1 << idx)) != 0;

        // AddChunkChainingValue appends a chunk to the right edge of the Merkle tree.
        private void AddChunkChainingValue(uint[] cv)
        {
            // seek to first open stack slot, merging subtrees as we go
            var idx = 0;
            while (HasSubTreeAtHeight(idx))
            {
                cv = Blake3Compressor.ComputeChainingValue(cv: Key,
                                                           block: ArrayUtils.Concatenate(Stack[idx], cv),
                                                           flags: Flags | flagParent,
                                                           blockLen: BlockSizeInBytes,
                                                           counter: 0);
                idx++;
            }

            Stack[idx] = ArrayUtils.Clone(cv);
            Used++;
        }

        private static byte Len8(byte value)
        {
            byte result = 0;
            while (value != 0)
            {
                value = (byte) (value >> 1);
                result++;
            }

            return result;
        }

        // Len64 returns the minimum number of bits required to represent x; the result is 0 for x == 0.
        private static int Len64(ulong value)
        {
            var result = 0;
            if (value >= 1)
            {
                value >>= 32;
                result = 32;
            }

            if (value >= 1 << 16)
            {
                value >>= 16;
                result += 16;
            }

            if (value < 1 << 8) return result + Len8((byte) value);
            value >>= 8;
            result += 8;

            return result + Len8((byte) value);
        }

        private static int TrailingZeros64(ulong value)
        {
            if (value == 0) return 64;

            var result = 0;
            while ((value & 1) == 0)
            {
                value >>= 1;
                result++;
            }

            return result;
        }

        public override string Name => $"{GetType().Name}_{HashSize * 8}";

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        protected void InternalDoOutput(byte[] dest, ulong destOffset, ulong outputLength) =>
            OutputReader.Read(dest, destOffset, outputLength);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        protected void Finish() => OutputReader.N = RootNode();

        private static unsafe uint[] InternalSetup(byte[] key)
        {
            if (key.Length == 0)
            {
                return ArrayUtils.Clone(IV);
            }

            var keyLength = key.Length;
            var result = new uint[8];
            if (keyLength != KeyLengthInBytes)
                throw new ArgumentException(
                    string.Format(InvalidKeyLength, KeyLengthInBytes, keyLength));

            fixed (byte* keyPtr = key)
            {
                fixed (uint* resultPtr = result)
                {
                    Converters.le32_copy(keyPtr, 0, resultPtr, 0, keyLength);
                }
            }

            return result;
        }

        internal Blake3(int hashSize, uint[] keyWords, uint flags)
            : base(hashSize, BlockSizeInBytes)
        {
            Key = ArrayUtils.Clone(keyWords);
            Flags = flags;

            Stack = new uint[54][];
            for (var idx = 0; idx < Stack.Length; idx++)
                Stack[idx] = new uint[8];
        }

        protected Blake3(int hashSize, byte[] key) : this(hashSize,
            key != null ? InternalSetup(key) : throw new ArgumentNullException(nameof(key)),
            key.Length == 0 ? 0 : flagKeyedHash)
        {
        }

        internal Blake3(HashSize hashSize, byte[] key) : this((int) hashSize,
            key ?? throw new ArgumentNullException(nameof(key)))
        {
        }

        public override void Initialize()
        {
            ChunkState = Blake3ChunkState.CreateBlake3ChunkState(Key, 0, Flags);
            OutputReader = Blake3OutputReader.DefaultBlake3OutputReader();
            ArrayUtils.ZeroFill(Stack);
            Used = 0;
        }

        public override void TransformBytes(byte[] data, int index, int length)
        {
            if (data == null) throw new ArgumentNullException(nameof(data));
            Debug.Assert(index >= 0);
            Debug.Assert(length >= 0);
            Debug.Assert(index + length <= data.Length);

            var dataSpan = new ReadOnlySpan<byte>(data, index, length);

            while (length > 0)
            {
                // If the current chunk is complete, finalize it and add it to the tree,
                // then reset the chunk state (but keep incrementing the counter across
                // chunks).
                if (ChunkState.IsComplete)
                {
                    AddChunkChainingValue(ChunkState.ComputeChunkEndChainingValue());
                    ChunkState =
                        Blake3ChunkState.CreateBlake3ChunkState(Key, ChunkState.ChunkCounter() + 1, Flags);
                }

                // Compress input bytes into the current chunk state.
                var count = Math.Min(ChunkSize - ChunkState.BytesConsumed, length);
                ChunkState.Update(dataSpan.Slice(0, count));

                dataSpan = dataSpan.Slice(count);
                length -= count;
            }
        }

        public override IHashResult TransformFinal()
        {
            Finish();

            var buffer = new byte[HashSize];

            InternalDoOutput(buffer, 0, (ulong) buffer.Length);

            IHashResult result = new HashResult(buffer);

            Initialize();

            return result;
        }

        public override IHash Clone() =>
            new Blake3(HashSize, Key, Flags)
            {
                ChunkState = ChunkState?.Clone(),
                OutputReader = OutputReader?.Clone(),
                Stack = ArrayUtils.Clone(Stack),
                Used = Used,
                BufferSize = BufferSize
            };
    }

    internal sealed class Blake3XOF : Blake3, IXOF
    {
        private const string InvalidXofSize = "XOFSizeInBits must be multiples of 8 and be greater than zero bytes";
        private const string InvalidOutputLength = "Output length is above the digest length";
        private const string OutputBufferTooShort = "Output buffer too short";
        private const string WriteToXofAfterReadError = "\"{0}\" write to Xof after read not allowed";

        private bool _finalized;
        private ulong _xofSizeInBits;

        public ulong XofSizeInBits
        {
            get => _xofSizeInBits;
            set => SetXofSizeInBitsInternal(value);
        }

        internal Blake3XOF(int hashSize, byte[] key) : base(hashSize, key)
        {
        }

        internal Blake3XOF(int hashSize, uint[] keyWords, uint flags)
            : base(hashSize, keyWords, flags)
        {
        }

        public override string Name => GetType().Name;

        public override void Initialize()
        {
            _finalized = false;
            base.Initialize();
        }

        public override IHash Clone() =>
            new Blake3XOF(HashSize, new byte[0])
            {
                // Blake3 Cloning
                ChunkState = ChunkState?.Clone(),
                OutputReader = OutputReader?.Clone(),
                Stack = ArrayUtils.Clone(Stack),
                Used = Used,
                Flags = Flags,
                Key = ArrayUtils.Clone(Key),
                BufferSize = BufferSize,
                // Blake3XOF Cloning
                _finalized = _finalized,
                // Xof Cloning
                XofSizeInBits = XofSizeInBits
            };

        public override void TransformBytes(byte[] data, int index, int length)
        {
            if (_finalized)
                throw new InvalidOperationException(
                    string.Format(WriteToXofAfterReadError, Name));

            base.TransformBytes(data, index, length);
        }

        public override IHashResult TransformFinal()
        {
            var buffer = GetResult();
            Debug.Assert((ulong) buffer.Length == XofSizeInBits >> 3);
            Initialize();

            var result = new HashResult(buffer);

            return result;
        }

        public void DoOutput(byte[] dest, ulong destOffset, ulong outputLength)
        {
            if (dest == null) throw new ArgumentNullException(nameof(dest));

            if ((ulong) dest.Length - destOffset < outputLength)
                throw new ArgumentException(OutputBufferTooShort);

            if (OutputReader.Offset + outputLength > XofSizeInBits >> 3)
                throw new ArgumentException(InvalidOutputLength);

            if (!_finalized)
            {
                Finish();
                _finalized = true;
            }

            InternalDoOutput(dest, destOffset, outputLength);
        }

        private void SetXofSizeInBitsInternal(ulong xofSizeInBits)
        {
            var xofSizeInBytes = xofSizeInBits >> 3;
            if ((xofSizeInBits & 0x7) != 0 || xofSizeInBytes < 1)
                throw new ArgumentException(InvalidXofSize);

            _xofSizeInBits = xofSizeInBits;
        }

        private byte[] GetResult()
        {
            var xofSizeInBytes = XofSizeInBits >> 3;

            var result = new byte[xofSizeInBytes];

            DoOutput(result, 0, xofSizeInBytes);

            return result;
        }
    }
}