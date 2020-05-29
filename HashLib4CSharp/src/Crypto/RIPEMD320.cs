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

using HashLib4CSharp.Interfaces;
using HashLib4CSharp.Utils;

namespace HashLib4CSharp.Crypto
{
    internal sealed class RIPEMD320 : MDBase, ITransformBlock
    {
        internal RIPEMD320()
            : base(10, 40)
        {
        }

        public override IHash Clone() =>
            new RIPEMD320
            {
                State = ArrayUtils.Clone(State),
                Buffer = Buffer.Clone(),
                ProcessedBytesCount = ProcessedBytesCount,
                BufferSize = BufferSize
            };

        public override void Initialize()
        {
            State[4] = 0xC3D2E1F0;
            State[5] = 0x76543210;
            State[6] = 0xFEDCBA98;
            State[7] = 0x89ABCDEF;
            State[8] = 0x01234567;
            State[9] = 0x3C2D1E0F;

            base.Initialize();
        }

        protected override unsafe void TransformBlock(void* data,
            int dataLength, int index)
        {
            var buffer = new uint[16];

            fixed (uint* bufferPtr = buffer)
            {
                Converters.le32_copy(data, index, bufferPtr, 0, dataLength);
            }

            var a = State[0];
            var b = State[1];
            var c = State[2];
            var d = State[3];
            var e = State[4];
            var aa = State[5];
            var bb = State[6];
            var cc = State[7];
            var dd = State[8];
            var ee = State[9];

            a += buffer[0] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 11) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[1] + (a ^ b ^ c);
            e = Bits.RotateLeft32(e, 14) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[2] + (e ^ a ^ b);
            d = Bits.RotateLeft32(d, 15) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[3] + (d ^ e ^ a);
            c = Bits.RotateLeft32(c, 12) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[4] + (c ^ d ^ e);
            b = Bits.RotateLeft32(b, 5) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[5] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 8) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[6] + (a ^ b ^ c);
            e = Bits.RotateLeft32(e, 7) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[7] + (e ^ a ^ b);
            d = Bits.RotateLeft32(d, 9) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[8] + (d ^ e ^ a);
            c = Bits.RotateLeft32(c, 11) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[9] + (c ^ d ^ e);
            b = Bits.RotateLeft32(b, 13) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[10] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 14) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[11] + (a ^ b ^ c);
            e = Bits.RotateLeft32(e, 15) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[12] + (e ^ a ^ b);
            d = Bits.RotateLeft32(d, 6) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[13] + (d ^ e ^ a);
            c = Bits.RotateLeft32(c, 7) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[14] + (c ^ d ^ e);
            b = Bits.RotateLeft32(b, 9) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[15] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 8) + e;
            c = Bits.RotateLeft32(c, 10);

            aa += buffer[5] + C1 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 8) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[14] + C1 + (aa ^ (bb | ~cc));
            ee = Bits.RotateLeft32(ee, 9) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[7] + C1 + (ee ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 9) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[0] + C1 + (dd ^ (ee | ~aa));
            cc = Bits.RotateLeft32(cc, 11) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[9] + C1 + (cc ^ (dd | ~ee));
            bb = Bits.RotateLeft32(bb, 13) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[2] + C1 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 15) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[11] + C1 + (aa ^ (bb | ~cc));
            ee = Bits.RotateLeft32(ee, 15) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[4] + C1 + (ee ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 5) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[13] + C1 + (dd ^ (ee | ~aa));
            cc = Bits.RotateLeft32(cc, 7) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[6] + C1 + (cc ^ (dd | ~ee));
            bb = Bits.RotateLeft32(bb, 7) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[15] + C1 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 8) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[8] + C1 + (aa ^ (bb | ~cc));
            ee = Bits.RotateLeft32(ee, 11) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[1] + C1 + (ee ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 14) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[10] + C1 + (dd ^ (ee | ~aa));
            cc = Bits.RotateLeft32(cc, 14) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[3] + C1 + (cc ^ (dd | ~ee));
            bb = Bits.RotateLeft32(bb, 12) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[12] + C1 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 6) + ee;
            cc = Bits.RotateLeft32(cc, 10);

            e += buffer[7] + C2 + ((aa & b) | (~aa & c));
            e = Bits.RotateLeft32(e, 7) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[4] + C2 + ((e & aa) | (~e & b));
            d = Bits.RotateLeft32(d, 6) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[13] + C2 + ((d & e) | (~d & aa));
            c = Bits.RotateLeft32(c, 8) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[1] + C2 + ((c & d) | (~c & e));
            b = Bits.RotateLeft32(b, 13) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[10] + C2 + ((b & c) | (~b & d));
            aa = Bits.RotateLeft32(aa, 11) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[6] + C2 + ((aa & b) | (~aa & c));
            e = Bits.RotateLeft32(e, 9) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[15] + C2 + ((e & aa) | (~e & b));
            d = Bits.RotateLeft32(d, 7) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[3] + C2 + ((d & e) | (~d & aa));
            c = Bits.RotateLeft32(c, 15) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[12] + C2 + ((c & d) | (~c & e));
            b = Bits.RotateLeft32(b, 7) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[0] + C2 + ((b & c) | (~b & d));
            aa = Bits.RotateLeft32(aa, 12) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[9] + C2 + ((aa & b) | (~aa & c));
            e = Bits.RotateLeft32(e, 15) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[5] + C2 + ((e & aa) | (~e & b));
            d = Bits.RotateLeft32(d, 9) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[2] + C2 + ((d & e) | (~d & aa));
            c = Bits.RotateLeft32(c, 11) + b;
            e = Bits.RotateLeft32(e, 10);
            b += buffer[14] + C2 + ((c & d) | (~c & e));
            b = Bits.RotateLeft32(b, 7) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[11] + C2 + ((b & c) | (~b & d));
            aa = Bits.RotateLeft32(aa, 13) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[8] + C2 + ((aa & b) | (~aa & c));
            e = Bits.RotateLeft32(e, 12) + d;
            b = Bits.RotateLeft32(b, 10);

            ee += buffer[6] + C3 + ((a & cc) | (bb & ~cc));
            ee = Bits.RotateLeft32(ee, 9) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[11] + C3 + ((ee & bb) | (a & ~bb));
            dd = Bits.RotateLeft32(dd, 13) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[3] + C3 + ((dd & a) | (ee & ~a));
            cc = Bits.RotateLeft32(cc, 15) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[7] + C3 + ((cc & ee) | (dd & ~ee));
            bb = Bits.RotateLeft32(bb, 7) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[0] + C3 + ((bb & dd) | (cc & ~dd));
            a = Bits.RotateLeft32(a, 12) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[13] + C3 + ((a & cc) | (bb & ~cc));
            ee = Bits.RotateLeft32(ee, 8) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[5] + C3 + ((ee & bb) | (a & ~bb));
            dd = Bits.RotateLeft32(dd, 9) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[10] + C3 + ((dd & a) | (ee & ~a));
            cc = Bits.RotateLeft32(cc, 11) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[14] + C3 + ((cc & ee) | (dd & ~ee));
            bb = Bits.RotateLeft32(bb, 7) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[15] + C3 + ((bb & dd) | (cc & ~dd));
            a = Bits.RotateLeft32(a, 7) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[8] + C3 + ((a & cc) | (bb & ~cc));
            ee = Bits.RotateLeft32(ee, 12) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[12] + C3 + ((ee & bb) | (a & ~bb));
            dd = Bits.RotateLeft32(dd, 7) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[4] + C3 + ((dd & a) | (ee & ~a));
            cc = Bits.RotateLeft32(cc, 6) + bb;
            ee = Bits.RotateLeft32(ee, 10);
            bb += buffer[9] + C3 + ((cc & ee) | (dd & ~ee));
            bb = Bits.RotateLeft32(bb, 15) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[1] + C3 + ((bb & dd) | (cc & ~dd));
            a = Bits.RotateLeft32(a, 13) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[2] + C3 + ((a & cc) | (bb & ~cc));
            ee = Bits.RotateLeft32(ee, 11) + dd;
            bb = Bits.RotateLeft32(bb, 10);

            d += buffer[3] + C4 + ((e | ~aa) ^ bb);
            d = Bits.RotateLeft32(d, 11) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[10] + C4 + ((d | ~e) ^ aa);
            c = Bits.RotateLeft32(c, 13) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[14] + C4 + ((c | ~d) ^ e);
            bb = Bits.RotateLeft32(bb, 6) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[4] + C4 + ((bb | ~c) ^ d);
            aa = Bits.RotateLeft32(aa, 7) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[9] + C4 + ((aa | ~bb) ^ c);
            e = Bits.RotateLeft32(e, 14) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[15] + C4 + ((e | ~aa) ^ bb);
            d = Bits.RotateLeft32(d, 9) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[8] + C4 + ((d | ~e) ^ aa);
            c = Bits.RotateLeft32(c, 13) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[1] + C4 + ((c | ~d) ^ e);
            bb = Bits.RotateLeft32(bb, 15) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[2] + C4 + ((bb | ~c) ^ d);
            aa = Bits.RotateLeft32(aa, 14) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[7] + C4 + ((aa | ~bb) ^ c);
            e = Bits.RotateLeft32(e, 8) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[0] + C4 + ((e | ~aa) ^ bb);
            d = Bits.RotateLeft32(d, 13) + c;
            aa = Bits.RotateLeft32(aa, 10);
            c += buffer[6] + C4 + ((d | ~e) ^ aa);
            c = Bits.RotateLeft32(c, 6) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[13] + C4 + ((c | ~d) ^ e);
            bb = Bits.RotateLeft32(bb, 5) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[11] + C4 + ((bb | ~c) ^ d);
            aa = Bits.RotateLeft32(aa, 12) + e;
            c = Bits.RotateLeft32(c, 10);
            e += buffer[5] + C4 + ((aa | ~bb) ^ c);
            e = Bits.RotateLeft32(e, 7) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[12] + C4 + ((e | ~aa) ^ bb);
            d = Bits.RotateLeft32(d, 5) + c;
            aa = Bits.RotateLeft32(aa, 10);

            dd += buffer[15] + C5 + ((ee | ~a) ^ b);
            dd = Bits.RotateLeft32(dd, 9) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[5] + C5 + ((dd | ~ee) ^ a);
            cc = Bits.RotateLeft32(cc, 7) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[1] + C5 + ((cc | ~dd) ^ ee);
            b = Bits.RotateLeft32(b, 15) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[3] + C5 + ((b | ~cc) ^ dd);
            a = Bits.RotateLeft32(a, 11) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[7] + C5 + ((a | ~b) ^ cc);
            ee = Bits.RotateLeft32(ee, 8) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[14] + C5 + ((ee | ~a) ^ b);
            dd = Bits.RotateLeft32(dd, 6) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[6] + C5 + ((dd | ~ee) ^ a);
            cc = Bits.RotateLeft32(cc, 6) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[9] + C5 + ((cc | ~dd) ^ ee);
            b = Bits.RotateLeft32(b, 14) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[11] + C5 + ((b | ~cc) ^ dd);
            a = Bits.RotateLeft32(a, 12) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[8] + C5 + ((a | ~b) ^ cc);
            ee = Bits.RotateLeft32(ee, 13) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[12] + C5 + ((ee | ~a) ^ b);
            dd = Bits.RotateLeft32(dd, 5) + cc;
            a = Bits.RotateLeft32(a, 10);
            cc += buffer[2] + C5 + ((dd | ~ee) ^ a);
            cc = Bits.RotateLeft32(cc, 14) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[10] + C5 + ((cc | ~dd) ^ ee);
            b = Bits.RotateLeft32(b, 13) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[0] + C5 + ((b | ~cc) ^ dd);
            a = Bits.RotateLeft32(a, 13) + ee;
            cc = Bits.RotateLeft32(cc, 10);
            ee += buffer[4] + C5 + ((a | ~b) ^ cc);
            ee = Bits.RotateLeft32(ee, 7) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[13] + C5 + ((ee | ~a) ^ b);
            dd = Bits.RotateLeft32(dd, 5) + cc;
            a = Bits.RotateLeft32(a, 10);

            cc += buffer[1] + C6 + ((d & aa) | (e & ~aa));
            cc = Bits.RotateLeft32(cc, 11) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[9] + C6 + ((cc & e) | (d & ~e));
            bb = Bits.RotateLeft32(bb, 12) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[11] + C6 + ((bb & d) | (cc & ~d));
            aa = Bits.RotateLeft32(aa, 14) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[10] + C6 + ((aa & cc) | (bb & ~cc));
            e = Bits.RotateLeft32(e, 15) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[0] + C6 + ((e & bb) | (aa & ~bb));
            d = Bits.RotateLeft32(d, 14) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[8] + C6 + ((d & aa) | (e & ~aa));
            cc = Bits.RotateLeft32(cc, 15) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[12] + C6 + ((cc & e) | (d & ~e));
            bb = Bits.RotateLeft32(bb, 9) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[4] + C6 + ((bb & d) | (cc & ~d));
            aa = Bits.RotateLeft32(aa, 8) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[13] + C6 + ((aa & cc) | (bb & ~cc));
            e = Bits.RotateLeft32(e, 9) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[3] + C6 + ((e & bb) | (aa & ~bb));
            d = Bits.RotateLeft32(d, 14) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[7] + C6 + ((d & aa) | (e & ~aa));
            cc = Bits.RotateLeft32(cc, 5) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[15] + C6 + ((cc & e) | (d & ~e));
            bb = Bits.RotateLeft32(bb, 6) + aa;
            d = Bits.RotateLeft32(d, 10);
            aa += buffer[14] + C6 + ((bb & d) | (cc & ~d));
            aa = Bits.RotateLeft32(aa, 8) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[5] + C6 + ((aa & cc) | (bb & ~cc));
            e = Bits.RotateLeft32(e, 6) + d;
            bb = Bits.RotateLeft32(bb, 10);
            d += buffer[6] + C6 + ((e & bb) | (aa & ~bb));
            d = Bits.RotateLeft32(d, 5) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[2] + C6 + ((d & aa) | (e & ~aa));
            cc = Bits.RotateLeft32(cc, 12) + bb;
            e = Bits.RotateLeft32(e, 10);

            c += buffer[8] + C7 + ((dd & ee) | (~dd & a));
            c = Bits.RotateLeft32(c, 15) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[6] + C7 + ((c & dd) | (~c & ee));
            b = Bits.RotateLeft32(b, 5) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[4] + C7 + ((b & c) | (~b & dd));
            a = Bits.RotateLeft32(a, 8) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[1] + C7 + ((a & b) | (~a & c));
            ee = Bits.RotateLeft32(ee, 11) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[3] + C7 + ((ee & a) | (~ee & b));
            dd = Bits.RotateLeft32(dd, 14) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[11] + C7 + ((dd & ee) | (~dd & a));
            c = Bits.RotateLeft32(c, 14) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[15] + C7 + ((c & dd) | (~c & ee));
            b = Bits.RotateLeft32(b, 6) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[0] + C7 + ((b & c) | (~b & dd));
            a = Bits.RotateLeft32(a, 14) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[5] + C7 + ((a & b) | (~a & c));
            ee = Bits.RotateLeft32(ee, 6) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[12] + C7 + ((ee & a) | (~ee & b));
            dd = Bits.RotateLeft32(dd, 9) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[2] + C7 + ((dd & ee) | (~dd & a));
            c = Bits.RotateLeft32(c, 12) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[13] + C7 + ((c & dd) | (~c & ee));
            b = Bits.RotateLeft32(b, 9) + a;
            dd = Bits.RotateLeft32(dd, 10);
            a += buffer[9] + C7 + ((b & c) | (~b & dd));
            a = Bits.RotateLeft32(a, 12) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[7] + C7 + ((a & b) | (~a & c));
            ee = Bits.RotateLeft32(ee, 5) + dd;
            b = Bits.RotateLeft32(b, 10);
            dd += buffer[10] + C7 + ((ee & a) | (~ee & b));
            dd = Bits.RotateLeft32(dd, 15) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[14] + C7 + ((dd & ee) | (~dd & a));
            c = Bits.RotateLeft32(c, 8) + b;
            ee = Bits.RotateLeft32(ee, 10);

            bb += buffer[4] + C8 + (cc ^ (dd | ~e));
            bb = Bits.RotateLeft32(bb, 9) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[0] + C8 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 15) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[5] + C8 + (aa ^ (bb | ~cc));
            e = Bits.RotateLeft32(e, 5) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[9] + C8 + (e ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 11) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[7] + C8 + (dd ^ (e | ~aa));
            cc = Bits.RotateLeft32(cc, 6) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[12] + C8 + (cc ^ (dd | ~e));
            bb = Bits.RotateLeft32(bb, 8) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[2] + C8 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 13) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[10] + C8 + (aa ^ (bb | ~cc));
            e = Bits.RotateLeft32(e, 12) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[14] + C8 + (e ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 5) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[1] + C8 + (dd ^ (e | ~aa));
            cc = Bits.RotateLeft32(cc, 12) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[3] + C8 + (cc ^ (dd | ~e));
            bb = Bits.RotateLeft32(bb, 13) + aa;
            dd = Bits.RotateLeft32(dd, 10);
            aa += buffer[8] + C8 + (bb ^ (cc | ~dd));
            aa = Bits.RotateLeft32(aa, 14) + e;
            cc = Bits.RotateLeft32(cc, 10);
            e += buffer[11] + C8 + (aa ^ (bb | ~cc));
            e = Bits.RotateLeft32(e, 11) + dd;
            bb = Bits.RotateLeft32(bb, 10);
            dd += buffer[6] + C8 + (e ^ (aa | ~bb));
            dd = Bits.RotateLeft32(dd, 8) + cc;
            aa = Bits.RotateLeft32(aa, 10);
            cc += buffer[15] + C8 + (dd ^ (e | ~aa));
            cc = Bits.RotateLeft32(cc, 5) + bb;
            e = Bits.RotateLeft32(e, 10);
            bb += buffer[13] + C8 + (cc ^ (dd | ~e));
            bb = Bits.RotateLeft32(bb, 6) + aa;
            dd = Bits.RotateLeft32(dd, 10);

            b += buffer[12] + (c ^ d ^ ee);
            b = Bits.RotateLeft32(b, 8) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[15] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 5) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[10] + (a ^ b ^ c);
            ee = Bits.RotateLeft32(ee, 12) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[4] + (ee ^ a ^ b);
            d = Bits.RotateLeft32(d, 9) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[1] + (d ^ ee ^ a);
            c = Bits.RotateLeft32(c, 12) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[5] + (c ^ d ^ ee);
            b = Bits.RotateLeft32(b, 5) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[8] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 14) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[7] + (a ^ b ^ c);
            ee = Bits.RotateLeft32(ee, 6) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[6] + (ee ^ a ^ b);
            d = Bits.RotateLeft32(d, 8) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[2] + (d ^ ee ^ a);
            c = Bits.RotateLeft32(c, 13) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[13] + (c ^ d ^ ee);
            b = Bits.RotateLeft32(b, 6) + a;
            d = Bits.RotateLeft32(d, 10);
            a += buffer[14] + (b ^ c ^ d);
            a = Bits.RotateLeft32(a, 5) + ee;
            c = Bits.RotateLeft32(c, 10);
            ee += buffer[0] + (a ^ b ^ c);
            ee = Bits.RotateLeft32(ee, 15) + d;
            b = Bits.RotateLeft32(b, 10);
            d += buffer[3] + (ee ^ a ^ b);
            d = Bits.RotateLeft32(d, 13) + c;
            a = Bits.RotateLeft32(a, 10);
            c += buffer[9] + (d ^ ee ^ a);
            c = Bits.RotateLeft32(c, 11) + b;
            ee = Bits.RotateLeft32(ee, 10);
            b += buffer[11] + (c ^ d ^ ee);
            b = Bits.RotateLeft32(b, 11) + a;
            d = Bits.RotateLeft32(d, 10);

            State[0] = State[0] + aa;
            State[1] = State[1] + bb;
            State[2] = State[2] + cc;
            State[3] = State[3] + dd;
            State[4] = State[4] + ee;
            State[5] = State[5] + a;
            State[6] = State[6] + b;
            State[7] = State[7] + c;
            State[8] = State[8] + d;
            State[9] = State[9] + e;

            ArrayUtils.ZeroFill(buffer);
        }
    }
}