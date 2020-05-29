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
using System.Runtime.CompilerServices;
using HashLib4CSharp.Base;
using HashLib4CSharp.Interfaces;
using HashLib4CSharp.Utils;

namespace HashLib4CSharp.Crypto
{
    internal abstract class GOST3411_2012 : Hash, ICryptoNotBuiltIn, ITransformBlock
    {
        private static readonly byte[] Zero =
        {
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
        };

        private static readonly byte[][] C =
        {
            new[]
            {
                (byte) 0xB1,
                (byte) 0x08, (byte) 0x5B, (byte) 0xDA, (byte) 0x1E, (byte) 0xCA, (byte) 0xDA, (byte) 0xE9,
                (byte) 0xEB, (byte) 0xCB, (byte) 0x2F, (byte) 0x81, (byte) 0xC0, (byte) 0x65, (byte) 0x7C,
                (byte) 0x1F, (byte) 0x2F, (byte) 0x6A, (byte) 0x76, (byte) 0x43, (byte) 0x2E, (byte) 0x45,
                (byte) 0xD0, (byte) 0x16, (byte) 0x71, (byte) 0x4E, (byte) 0xB8, (byte) 0x8D, (byte) 0x75,
                (byte) 0x85, (byte) 0xC4, (byte) 0xFC, (byte) 0x4B, (byte) 0x7C, (byte) 0xE0, (byte) 0x91,
                (byte) 0x92, (byte) 0x67, (byte) 0x69, (byte) 0x01, (byte) 0xA2, (byte) 0x42, (byte) 0x2A,
                (byte) 0x08, (byte) 0xA4, (byte) 0x60, (byte) 0xD3, (byte) 0x15, (byte) 0x05, (byte) 0x76,
                (byte) 0x74, (byte) 0x36, (byte) 0xCC, (byte) 0x74, (byte) 0x4D, (byte) 0x23, (byte) 0xDD,
                (byte) 0x80, (byte) 0x65, (byte) 0x59, (byte) 0xF2, (byte) 0xA6, (byte) 0x45,
                (byte) 0x07
            },

            new[]
            {
                (byte) 0x6F, (byte) 0xA3, (byte) 0xB5, (byte) 0x8A,
                (byte) 0xA9, (byte) 0x9D, (byte) 0x2F, (byte) 0x1A, (byte) 0x4F, (byte) 0xE3, (byte) 0x9D,
                (byte) 0x46, (byte) 0x0F, (byte) 0x70, (byte) 0xB5, (byte) 0xD7, (byte) 0xF3, (byte) 0xFE,
                (byte) 0xEA, (byte) 0x72, (byte) 0x0A, (byte) 0x23, (byte) 0x2B, (byte) 0x98, (byte) 0x61,
                (byte) 0xD5, (byte) 0x5E, (byte) 0x0F, (byte) 0x16, (byte) 0xB5, (byte) 0x01, (byte) 0x31,
                (byte) 0x9A, (byte) 0xB5, (byte) 0x17, (byte) 0x6B, (byte) 0x12, (byte) 0xD6, (byte) 0x99,
                (byte) 0x58, (byte) 0x5C, (byte) 0xB5, (byte) 0x61, (byte) 0xC2, (byte) 0xDB, (byte) 0x0A,
                (byte) 0xA7, (byte) 0xCA, (byte) 0x55, (byte) 0xDD, (byte) 0xA2, (byte) 0x1B, (byte) 0xD7,
                (byte) 0xCB, (byte) 0xCD, (byte) 0x56, (byte) 0xE6, (byte) 0x79, (byte) 0x04, (byte) 0x70,
                (byte) 0x21, (byte) 0xB1, (byte) 0x9B, (byte) 0xB7
            },

            new[]
            {
                (byte) 0xF5, (byte) 0x74, (byte) 0xDC, (byte) 0xAC,
                (byte) 0x2B, (byte) 0xCE, (byte) 0x2F, (byte) 0xC7, (byte) 0x0A, (byte) 0x39, (byte) 0xFC,
                (byte) 0x28, (byte) 0x6A, (byte) 0x3D, (byte) 0x84, (byte) 0x35, (byte) 0x06, (byte) 0xF1,
                (byte) 0x5E, (byte) 0x5F, (byte) 0x52, (byte) 0x9C, (byte) 0x1F, (byte) 0x8B, (byte) 0xF2,
                (byte) 0xEA, (byte) 0x75, (byte) 0x14, (byte) 0xB1, (byte) 0x29, (byte) 0x7B, (byte) 0x7B,
                (byte) 0xD3, (byte) 0xE2, (byte) 0x0F, (byte) 0xE4, (byte) 0x90, (byte) 0x35, (byte) 0x9E,
                (byte) 0xB1, (byte) 0xC1, (byte) 0xC9, (byte) 0x3A, (byte) 0x37, (byte) 0x60, (byte) 0x62,
                (byte) 0xDB, (byte) 0x09, (byte) 0xC2, (byte) 0xB6, (byte) 0xF4, (byte) 0x43, (byte) 0x86,
                (byte) 0x7A, (byte) 0xDB, (byte) 0x31, (byte) 0x99, (byte) 0x1E, (byte) 0x96, (byte) 0xF5,
                (byte) 0x0A, (byte) 0xBA, (byte) 0x0A, (byte) 0xB2
            },

            new[]
            {
                (byte) 0xEF, (byte) 0x1F, (byte) 0xDF, (byte) 0xB3,
                (byte) 0xE8, (byte) 0x15, (byte) 0x66, (byte) 0xD2, (byte) 0xF9, (byte) 0x48, (byte) 0xE1,
                (byte) 0xA0, (byte) 0x5D, (byte) 0x71, (byte) 0xE4, (byte) 0xDD, (byte) 0x48, (byte) 0x8E,
                (byte) 0x85, (byte) 0x7E, (byte) 0x33, (byte) 0x5C, (byte) 0x3C, (byte) 0x7D, (byte) 0x9D,
                (byte) 0x72, (byte) 0x1C, (byte) 0xAD, (byte) 0x68, (byte) 0x5E, (byte) 0x35, (byte) 0x3F,
                (byte) 0xA9, (byte) 0xD7, (byte) 0x2C, (byte) 0x82, (byte) 0xED, (byte) 0x03, (byte) 0xD6,
                (byte) 0x75, (byte) 0xD8, (byte) 0xB7, (byte) 0x13, (byte) 0x33, (byte) 0x93, (byte) 0x52,
                (byte) 0x03, (byte) 0xBE, (byte) 0x34, (byte) 0x53, (byte) 0xEA, (byte) 0xA1, (byte) 0x93,
                (byte) 0xE8, (byte) 0x37, (byte) 0xF1, (byte) 0x22, (byte) 0x0C, (byte) 0xBE, (byte) 0xBC,
                (byte) 0x84, (byte) 0xE3, (byte) 0xD1, (byte) 0x2E
            },

            new[]
            {
                (byte) 0x4B, (byte) 0xEA, (byte) 0x6B, (byte) 0xAC,
                (byte) 0xAD, (byte) 0x47, (byte) 0x47, (byte) 0x99, (byte) 0x9A, (byte) 0x3F, (byte) 0x41,
                (byte) 0x0C, (byte) 0x6C, (byte) 0xA9, (byte) 0x23, (byte) 0x63, (byte) 0x7F, (byte) 0x15,
                (byte) 0x1C, (byte) 0x1F, (byte) 0x16, (byte) 0x86, (byte) 0x10, (byte) 0x4A, (byte) 0x35,
                (byte) 0x9E, (byte) 0x35, (byte) 0xD7, (byte) 0x80, (byte) 0x0F, (byte) 0xFF, (byte) 0xBD,
                (byte) 0xBF, (byte) 0xCD, (byte) 0x17, (byte) 0x47, (byte) 0x25, (byte) 0x3A, (byte) 0xF5,
                (byte) 0xA3, (byte) 0xDF, (byte) 0xFF, (byte) 0x00, (byte) 0xB7, (byte) 0x23, (byte) 0x27,
                (byte) 0x1A, (byte) 0x16, (byte) 0x7A, (byte) 0x56, (byte) 0xA2, (byte) 0x7E, (byte) 0xA9,
                (byte) 0xEA, (byte) 0x63, (byte) 0xF5, (byte) 0x60, (byte) 0x17, (byte) 0x58, (byte) 0xFD,
                (byte) 0x7C, (byte) 0x6C, (byte) 0xFE, (byte) 0x57
            },

            new[]
            {
                (byte) 0xAE, (byte) 0x4F, (byte) 0xAE, (byte) 0xAE,
                (byte) 0x1D, (byte) 0x3A, (byte) 0xD3, (byte) 0xD9, (byte) 0x6F, (byte) 0xA4, (byte) 0xC3,
                (byte) 0x3B, (byte) 0x7A, (byte) 0x30, (byte) 0x39, (byte) 0xC0, (byte) 0x2D, (byte) 0x66,
                (byte) 0xC4, (byte) 0xF9, (byte) 0x51, (byte) 0x42, (byte) 0xA4, (byte) 0x6C, (byte) 0x18,
                (byte) 0x7F, (byte) 0x9A, (byte) 0xB4, (byte) 0x9A, (byte) 0xF0, (byte) 0x8E, (byte) 0xC6,
                (byte) 0xCF, (byte) 0xFA, (byte) 0xA6, (byte) 0xB7, (byte) 0x1C, (byte) 0x9A, (byte) 0xB7,
                (byte) 0xB4, (byte) 0x0A, (byte) 0xF2, (byte) 0x1F, (byte) 0x66, (byte) 0xC2, (byte) 0xBE,
                (byte) 0xC6, (byte) 0xB6, (byte) 0xBF, (byte) 0x71, (byte) 0xC5, (byte) 0x72, (byte) 0x36,
                (byte) 0x90, (byte) 0x4F, (byte) 0x35, (byte) 0xFA, (byte) 0x68, (byte) 0x40, (byte) 0x7A,
                (byte) 0x46, (byte) 0x64, (byte) 0x7D, (byte) 0x6E
            },

            new[]
            {
                (byte) 0xF4, (byte) 0xC7, (byte) 0x0E, (byte) 0x16,
                (byte) 0xEE, (byte) 0xAA, (byte) 0xC5, (byte) 0xEC, (byte) 0x51, (byte) 0xAC, (byte) 0x86,
                (byte) 0xFE, (byte) 0xBF, (byte) 0x24, (byte) 0x09, (byte) 0x54, (byte) 0x39, (byte) 0x9E,
                (byte) 0xC6, (byte) 0xC7, (byte) 0xE6, (byte) 0xBF, (byte) 0x87, (byte) 0xC9, (byte) 0xD3,
                (byte) 0x47, (byte) 0x3E, (byte) 0x33, (byte) 0x19, (byte) 0x7A, (byte) 0x93, (byte) 0xC9,
                (byte) 0x09, (byte) 0x92, (byte) 0xAB, (byte) 0xC5, (byte) 0x2D, (byte) 0x82, (byte) 0x2C,
                (byte) 0x37, (byte) 0x06, (byte) 0x47, (byte) 0x69, (byte) 0x83, (byte) 0x28, (byte) 0x4A,
                (byte) 0x05, (byte) 0x04, (byte) 0x35, (byte) 0x17, (byte) 0x45, (byte) 0x4C, (byte) 0xA2,
                (byte) 0x3C, (byte) 0x4A, (byte) 0xF3, (byte) 0x88, (byte) 0x86, (byte) 0x56, (byte) 0x4D,
                (byte) 0x3A, (byte) 0x14, (byte) 0xD4, (byte) 0x93
            },

            new[]
            {
                (byte) 0x9B, (byte) 0x1F, (byte) 0x5B, (byte) 0x42,
                (byte) 0x4D, (byte) 0x93, (byte) 0xC9, (byte) 0xA7, (byte) 0x03, (byte) 0xE7, (byte) 0xAA,
                (byte) 0x02, (byte) 0x0C, (byte) 0x6E, (byte) 0x41, (byte) 0x41, (byte) 0x4E, (byte) 0xB7,
                (byte) 0xF8, (byte) 0x71, (byte) 0x9C, (byte) 0x36, (byte) 0xDE, (byte) 0x1E, (byte) 0x89,
                (byte) 0xB4, (byte) 0x44, (byte) 0x3B, (byte) 0x4D, (byte) 0xDB, (byte) 0xC4, (byte) 0x9A,
                (byte) 0xF4, (byte) 0x89, (byte) 0x2B, (byte) 0xCB, (byte) 0x92, (byte) 0x9B, (byte) 0x06,
                (byte) 0x90, (byte) 0x69, (byte) 0xD1, (byte) 0x8D, (byte) 0x2B, (byte) 0xD1, (byte) 0xA5,
                (byte) 0xC4, (byte) 0x2F, (byte) 0x36, (byte) 0xAC, (byte) 0xC2, (byte) 0x35, (byte) 0x59,
                (byte) 0x51, (byte) 0xA8, (byte) 0xD9, (byte) 0xA4, (byte) 0x7F, (byte) 0x0D, (byte) 0xD4,
                (byte) 0xBF, (byte) 0x02, (byte) 0xE7, (byte) 0x1E
            },

            new[]
            {
                (byte) 0x37, (byte) 0x8F, (byte) 0x5A, (byte) 0x54,
                (byte) 0x16, (byte) 0x31, (byte) 0x22, (byte) 0x9B, (byte) 0x94, (byte) 0x4C, (byte) 0x9A,
                (byte) 0xD8, (byte) 0xEC, (byte) 0x16, (byte) 0x5F, (byte) 0xDE, (byte) 0x3A, (byte) 0x7D,
                (byte) 0x3A, (byte) 0x1B, (byte) 0x25, (byte) 0x89, (byte) 0x42, (byte) 0x24, (byte) 0x3C,
                (byte) 0xD9, (byte) 0x55, (byte) 0xB7, (byte) 0xE0, (byte) 0x0D, (byte) 0x09, (byte) 0x84,
                (byte) 0x80, (byte) 0x0A, (byte) 0x44, (byte) 0x0B, (byte) 0xDB, (byte) 0xB2, (byte) 0xCE,
                (byte) 0xB1, (byte) 0x7B, (byte) 0x2B, (byte) 0x8A, (byte) 0x9A, (byte) 0xA6, (byte) 0x07,
                (byte) 0x9C, (byte) 0x54, (byte) 0x0E, (byte) 0x38, (byte) 0xDC, (byte) 0x92, (byte) 0xCB,
                (byte) 0x1F, (byte) 0x2A, (byte) 0x60, (byte) 0x72, (byte) 0x61, (byte) 0x44, (byte) 0x51,
                (byte) 0x83, (byte) 0x23, (byte) 0x5A, (byte) 0xDB
            },

            new[]
            {
                (byte) 0xAB, (byte) 0xBE, (byte) 0xDE, (byte) 0xA6,
                (byte) 0x80, (byte) 0x05, (byte) 0x6F, (byte) 0x52, (byte) 0x38, (byte) 0x2A, (byte) 0xE5,
                (byte) 0x48, (byte) 0xB2, (byte) 0xE4, (byte) 0xF3, (byte) 0xF3, (byte) 0x89, (byte) 0x41,
                (byte) 0xE7, (byte) 0x1C, (byte) 0xFF, (byte) 0x8A, (byte) 0x78, (byte) 0xDB, (byte) 0x1F,
                (byte) 0xFF, (byte) 0xE1, (byte) 0x8A, (byte) 0x1B, (byte) 0x33, (byte) 0x61, (byte) 0x03,
                (byte) 0x9F, (byte) 0xE7, (byte) 0x67, (byte) 0x02, (byte) 0xAF, (byte) 0x69, (byte) 0x33,
                (byte) 0x4B, (byte) 0x7A, (byte) 0x1E, (byte) 0x6C, (byte) 0x30, (byte) 0x3B, (byte) 0x76,
                (byte) 0x52, (byte) 0xF4, (byte) 0x36, (byte) 0x98, (byte) 0xFA, (byte) 0xD1, (byte) 0x15,
                (byte) 0x3B, (byte) 0xB6, (byte) 0xC3, (byte) 0x74, (byte) 0xB4, (byte) 0xC7, (byte) 0xFB,
                (byte) 0x98, (byte) 0x45, (byte) 0x9C, (byte) 0xED
            },

            new[]
            {
                (byte) 0x7B, (byte) 0xCD, (byte) 0x9E, (byte) 0xD0,
                (byte) 0xEF, (byte) 0xC8, (byte) 0x89, (byte) 0xFB, (byte) 0x30, (byte) 0x02, (byte) 0xC6,
                (byte) 0xCD, (byte) 0x63, (byte) 0x5A, (byte) 0xFE, (byte) 0x94, (byte) 0xD8, (byte) 0xFA,
                (byte) 0x6B, (byte) 0xBB, (byte) 0xEB, (byte) 0xAB, (byte) 0x07, (byte) 0x61, (byte) 0x20,
                (byte) 0x01, (byte) 0x80, (byte) 0x21, (byte) 0x14, (byte) 0x84, (byte) 0x66, (byte) 0x79,
                (byte) 0x8A, (byte) 0x1D, (byte) 0x71, (byte) 0xEF, (byte) 0xEA, (byte) 0x48, (byte) 0xB9,
                (byte) 0xCA, (byte) 0xEF, (byte) 0xBA, (byte) 0xCD, (byte) 0x1D, (byte) 0x7D, (byte) 0x47,
                (byte) 0x6E, (byte) 0x98, (byte) 0xDE, (byte) 0xA2, (byte) 0x59, (byte) 0x4A, (byte) 0xC0,
                (byte) 0x6F, (byte) 0xD8, (byte) 0x5D, (byte) 0x6B, (byte) 0xCA, (byte) 0xA4, (byte) 0xCD,
                (byte) 0x81, (byte) 0xF3, (byte) 0x2D, (byte) 0x1B
            },

            new[]
            {
                (byte) 0x37, (byte) 0x8E, (byte) 0xE7, (byte) 0x67,
                (byte) 0xF1, (byte) 0x16, (byte) 0x31, (byte) 0xBA, (byte) 0xD2, (byte) 0x13, (byte) 0x80,
                (byte) 0xB0, (byte) 0x04, (byte) 0x49, (byte) 0xB1, (byte) 0x7A, (byte) 0xCD, (byte) 0xA4,
                (byte) 0x3C, (byte) 0x32, (byte) 0xBC, (byte) 0xDF, (byte) 0x1D, (byte) 0x77, (byte) 0xF8,
                (byte) 0x20, (byte) 0x12, (byte) 0xD4, (byte) 0x30, (byte) 0x21, (byte) 0x9F, (byte) 0x9B,
                (byte) 0x5D, (byte) 0x80, (byte) 0xEF, (byte) 0x9D, (byte) 0x18, (byte) 0x91, (byte) 0xCC,
                (byte) 0x86, (byte) 0xE7, (byte) 0x1D, (byte) 0xA4, (byte) 0xAA, (byte) 0x88, (byte) 0xE1,
                (byte) 0x28, (byte) 0x52, (byte) 0xFA, (byte) 0xF4, (byte) 0x17, (byte) 0xD5, (byte) 0xD9,
                (byte) 0xB2, (byte) 0x1B, (byte) 0x99, (byte) 0x48, (byte) 0xBC, (byte) 0x92, (byte) 0x4A,
                (byte) 0xF1, (byte) 0x1B, (byte) 0xD7, (byte) 0x20
            }
        };

        private static readonly ulong[][] T;
        protected int Offset;
        protected byte[] IV, N, Sigma, Ki, M, H, Tmp, Block;

        static GOST3411_2012()
        {
            T = new[]
            {
                new[]
                {
                    0xE6F87E5C5B711FD0,
                    (ulong) 0x258377800924FA16, 0xC849E07E852EA4A8,
                    (ulong) 0x5B4686A18F06C16A, (ulong) 0x0B32E9A2D77B416E,
                    0xABDA37A467815C66, 0xF61796A81A686676,
                    0xF5DC0B706391954B, (ulong) 0x4862F38DB7E64BF1,
                    0xFF5C629A68BD85C5, 0xCB827DA6FCD75795,
                    (ulong) 0x66D36DAF69B9F089, (ulong) 0x356C9F74483D83B0,
                    (ulong) 0x7CBCECB1238C99A1, (ulong) 0x36A702AC31C4708D,
                    0x9EB6A8D02FBCDFD6, 0x8B19FA51E5B3AE37,
                    0x9CCFB5408A127D0B, 0xBC0C78B508208F5A,
                    0xE533E3842288ECED, 0xCEC2C7D377C15FD2,
                    0xEC7817B6505D0F5E, 0xB94CC2C08336871D,
                    0x8C205DB4CB0B04AD, (ulong) 0x763C855B28A0892F,
                    (ulong) 0x588D1B79F6FF3257, (ulong) 0x3FECF69E4311933E,
                    (ulong) 0x0FC0D39F803A18C9, 0xEE010A26F5F3AD83,
                    (ulong) 0x10EFE8F4411979A6, (ulong) 0x5DCDA10C7DE93A10,
                    (ulong) 0x4A1BEE1D1248E92C, (ulong) 0x53BFF2DB21847339,
                    0xB4F50CCFA6A23D09, (ulong) 0x5FB4BC9CD84798CD,
                    0xE88A2D8B071C56F9, (ulong) 0x7F7771695A756A9C,
                    0xC5F02E71A0BA1EBC, 0xA663F9AB4215E672,
                    (ulong) 0x2EB19E22DE5FBB78, (ulong) 0x0DB9CE0F2594BA14,
                    0x82520E6397664D84, (ulong) 0x2F031E6A0208EA98,
                    (ulong) 0x5C7F2144A1BE6BF0, (ulong) 0x7A37CB1CD16362DB,
                    0x83E08E2B4B311C64, 0xCF70479BAB960E32,
                    0x856BA986B9DEE71E, 0xB5478C877AF56CE9,
                    0xB8FE42885F61D6FD, (ulong) 0x1BDD0156966238C8,
                    (ulong) 0x622157923EF8A92E, 0xFC97FF42114476F8,
                    0x9D7D350856452CEB, (ulong) 0x4C90C9B0E0A71256,
                    (ulong) 0x2308502DFBCB016C, (ulong) 0x2D7A03FAA7A64845,
                    0xF46E8B38BFC6C4AB, 0xBDBEF8FDD477DEBA,
                    (ulong) 0x3AAC4CEBC8079B79, 0xF09CB105E8879D0C,
                    (ulong) 0x27FA6A10AC8A58CB, 0x8960E7C1401D0CEA,
                    (ulong) 0x1A6F811E4A356928, 0x90C4FB0773D196FF,
                    (ulong) 0x43501A2F609D0A9F, 0xF7A516E0C63F3796,
                    (ulong) 0x1CE4A6B3B8DA9252, (ulong) 0x1324752C38E08A9B,
                    0xA5A864733BEC154F, (ulong) 0x2BF124575549B33F,
                    0xD766DB15440DC5C7, 0xA7D179E39E42B792,
                    0xDADF151A61997FD3, 0x86A0345EC0271423,
                    (ulong) 0x38D5517B6DA939A4, (ulong) 0x6518F077104003B4,
                    (ulong) 0x02791D90A5AEA2DD, 0x88D267899C4A5D0A,
                    0x930F66DF0A2865C2, (ulong) 0x4EE9D4204509B08B,
                    (ulong) 0x325538916685292A, (ulong) 0x412907BFC533A842,
                    0xB27E2B62544DC673, (ulong) 0x6C5304456295E007,
                    (ulong) 0x5AF406E95351908A, (ulong) 0x1F2F3B6BC123616F,
                    0xC37B09DC5255E5C6, (ulong) 0x3967D133B1FE6844,
                    (ulong) 0x298839C7F0E711E2, (ulong) 0x409B87F71964F9A2,
                    0xE938ADC3DB4B0719, (ulong) 0x0C0B4E47F9C3EBF4,
                    (ulong) 0x5534D576D36B8843, (ulong) 0x4610A05AEB8B02D8,
                    (ulong) 0x20C3CDF58232F251, (ulong) 0x6DE1840DBEC2B1E7,
                    0xA0E8DE06B0FA1D08, (ulong) 0x7B854B540D34333B,
                    (ulong) 0x42E29A67BCCA5B7F, 0xD8A6088AC437DD0E,
                    0xC63BB3A9D943ED81, (ulong) 0x21714DBD5E65A3B1,
                    (ulong) 0x6761EDE7B5EEA169, (ulong) 0x2431F7C8D573ABF6,
                    0xD51FC685E1A3671A, (ulong) 0x5E063CD40410C92D,
                    (ulong) 0x283AB98F2CB04002, 0x8FEBC06CB2F2F790,
                    (ulong) 0x17D64F116FA1D33C, 0xE07359F1A99EE4AA,
                    (ulong) 0x784ED68C74CDC006, (ulong) 0x6E2A19D5C73B42DA,
                    0x8712B4161C7045C3, (ulong) 0x371582E4ED93216D,
                    0xACE390414939F6FC, (ulong) 0x7EC5F12186223B7C,
                    0xC0B094042BAC16FB, 0xF9D745379A527EBF,
                    (ulong) 0x737C3F2EA3B68168, (ulong) 0x33E7B8D9BAD278CA,
                    0xA9A32A34C22FFEBB, 0xE48163CCFEDFBD0D,
                    0x8E5940246EA5A670, (ulong) 0x51C6EF4B842AD1E4,
                    (ulong) 0x22BAD065279C508C, 0xD91488C218608CEE,
                    (ulong) 0x319EA5491F7CDA17, 0xD394E128134C9C60,
                    (ulong) 0x094BF43272D5E3B3, 0x9BF612A5A4AAD791,
                    0xCCBBDA43D26FFD0F, (ulong) 0x34DE1F3C946AD250,
                    (ulong) 0x4F5B5468995EE16B, 0xDF9FAF6FEA8F7794,
                    (ulong) 0x2648EA5870DD092B, 0xBFC7E56D71D97C67,
                    0xDDE6B2FF4F21D549, (ulong) 0x3C276B463AE86003,
                    0x91767B4FAF86C71F, (ulong) 0x68A13E7835D4B9A0,
                    0xB68C115F030C9FD4, (ulong) 0x141DD2C916582001,
                    0x983D8F7DDD5324AC, (ulong) 0x64AA703FCC175254,
                    0xC2C989948E02B426, (ulong) 0x3E5E76D69F46C2DE,
                    (ulong) 0x50746F03587D8004, (ulong) 0x45DB3D829272F1E5,
                    (ulong) 0x60584A029B560BF3, 0xFBAE58A73FFCDC62,
                    0xA15A5E4E6CAD4CE8, (ulong) 0x4BA96E55CE1FB8CC,
                    (ulong) 0x08F9747AAE82B253, 0xC102144CF7FB471B,
                    0x9F042898F3EB8E36, (ulong) 0x068B27ADF2EFFB7A,
                    0xEDCA97FE8C0A5EBE, (ulong) 0x778E0513F4F7D8CF,
                    (ulong) 0x302C2501C32B8BF7, 0x8D92DDFC175C554D,
                    0xF865C57F46052F5F, 0xEAF3301BA2B2F424,
                    0xAA68B7ECBBD60D86, 0x998F0F350104754C,
                    (ulong) 0x0000000000000000, 0xF12E314D34D0CCEC,
                    (ulong) 0x710522BE061823B5, 0xAF280D9930C005C1,
                    0x97FD5CE25D693C65, (ulong) 0x19A41CC633CC9A15,
                    0x95844172F8C79EB8, 0xDC5432B7937684A9,
                    0x9436C13A2490CF58, 0x802B13F332C8EF59,
                    0xC442AE397CED4F5C, 0xFA1CD8EFE3AB8D82,
                    0xF2E5AC954D293FD1, (ulong) 0x6AD823E8907A1B7D,
                    (ulong) 0x4D2249F83CF043B6, (ulong) 0x03CB9DD879F9F33D,
                    0xDE2D2F2736D82674, (ulong) 0x2A43A41F891EE2DF,
                    (ulong) 0x6F98999D1B6C133A, 0xD4AD46CD3DF436FA,
                    0xBB35DF50269825C0, 0x964FDCAA813E6D85,
                    0xEB41B0537EE5A5C4, (ulong) 0x0540BA758B160847,
                    0xA41AE43BE7BB44AF, 0xE3B8C429D0671797,
                    0x819993BBEE9FBEB9, 0xAE9A8DD1EC975421,
                    0xF3572CDD917E6E31, (ulong) 0x6393D7DAE2AFF8CE,
                    (ulong) 0x47A2201237DC5338, 0xA32343DEC903EE35,
                    (ulong) 0x79FC56C4A89A91E6, (ulong) 0x01B28048DC5751E0,
                    (ulong) 0x1296F564E4B7DB7B, (ulong) 0x75F7188351597A12,
                    0xDB6D9552BDCE2E33, (ulong) 0x1E9DBB231D74308F,
                    (ulong) 0x520D7293FDD322D9, 0xE20A44610C304677,
                    0xFEEEE2D2B4EAD425, 0xCA30FDEE20800675,
                    (ulong) 0x61EACA4A47015A13, 0xE74AFE1487264E30,
                    (ulong) 0x2CC883B27BF119A5, (ulong) 0x1664CF59B3F682DC,
                    0xA811AA7C1E78AF5B, (ulong) 0x1D5626FB648DC3B2,
                    0xB73E9117DF5BCE34, 0xD05F7CF06AB56F5D,
                    0xFD257F0ACD132718, (ulong) 0x574DC8E676C52A9E,
                    (ulong) 0x0739A7E52EB8AA9A, (ulong) 0x5486553E0F3CD9A3,
                    (ulong) 0x56FF48AEAA927B7E, 0xBE756525AD8E2D87,
                    (ulong) 0x7D0E6CF9FFDBC841, (ulong) 0x3B1ECCA31450CA99,
                    (ulong) 0x6913BE30E983E840, 0xAD511009956EA71C,
                    0xB1B5B6BA2DB4354E, (ulong) 0x4469BDCA4E25A005,
                    (ulong) 0x15AF5281CA0F71E1, (ulong) 0x744598CB8D0E2BF2,
                    (ulong) 0x593F9B312AA863B7, 0xEFB38A6E29A4FC63,
                    (ulong) 0x6B6AA3A04C2D4A9D, (ulong) 0x3D95EB0EE6BF31E3,
                    0xA291C3961554BFD5, (ulong) 0x18169C8EEF9BCBF5,
                    (ulong) 0x115D68BC9D4E2846, 0xBA875F18FACF7420,
                    0xD1EDFCB8B6E23EBD, 0xB00736F2F1E364AE,
                    0x84D929CE6589B6FE, (ulong) 0x70B7A2F6DA4F7255,
                    (ulong) 0x0E7253D75C6D4929, (ulong) 0x04F23A3D574159A7,
                    (ulong) 0x0A8069EA0B2C108E, (ulong) 0x49D073C56BB11A11,
                    0x8AAB7A1939E4FFD7, 0xCD095A0B0E38ACEF,
                    0xC9FB60365979F548, 0x92BDE697D67F3422,
                    0xC78933E10514BC61, 0xE1C1D9B975C9B54A,
                    0xD2266160CF1BCD80, 0x9A4492ED78FD8671,
                    0xB3CCAB2A881A9793, (ulong) 0x72CEBF667FE1D088,
                    0xD6D45B5D985A9427
                },
                new[]
                {
                    0xC811A8058C3F55DE,
                    (ulong) 0x65F5B43196B50619, 0xF74F96B1D6706E43,
                    0x859D1E8BCB43D336, (ulong) 0x5AAB8A85CCFA3D84,
                    0xF9C7BF99C295FCFD, 0xA21FD5A1DE4B630F,
                    0xCDB3EF763B8B456D, 0x803F59F87CF7C385,
                    0xB27C73BE5F31913C, 0x98E3AC6633B04821,
                    0xBF61674C26B8F818, (ulong) 0x0FFBC995C4C130C8,
                    0xAAA0862010761A98, (ulong) 0x6057F342210116AA,
                    0xF63C760C0654CC35, (ulong) 0x2DDB45CC667D9042,
                    0xBCF45A964BD40382, (ulong) 0x68E8A0C3EF3C6F3D,
                    0xA7BD92D269FF73BC, (ulong) 0x290AE20201ED2287,
                    0xB7DE34CDE885818F, 0xD901EEA7DD61059B,
                    0xD6FA273219A03553, 0xD56F1AE874CCCEC9,
                    0xEA31245C2E83F554, (ulong) 0x7034555DA07BE499,
                    0xCE26D2AC56E7BEF7, 0xFD161857A5054E38,
                    (ulong) 0x6A0E7DA4527436D1, (ulong) 0x5BD86A381CDE9FF2,
                    0xCAF7756231770C32, 0xB09AAED9E279C8D0,
                    (ulong) 0x5DEF1091C60674DB, (ulong) 0x111046A2515E5045,
                    (ulong) 0x23536CE4729802FC, 0xC50CBCF7F5B63CFA,
                    (ulong) 0x73A16887CD171F03, (ulong) 0x7D2941AFD9F28DBD,
                    (ulong) 0x3F5E3EB45A4F3B9D, 0x84EEFE361B677140,
                    (ulong) 0x3DB8E3D3E7076271, (ulong) 0x1A3A28F9F20FD248,
                    (ulong) 0x7EBC7C75B49E7627, (ulong) 0x74E5F293C7EB565C,
                    (ulong) 0x18DCF59E4F478BA4, (ulong) 0x0C6EF44FA9ADCB52,
                    0xC699812D98DAC760, (ulong) 0x788B06DC6E469D0E,
                    0xFC65F8EA7521EC4E, (ulong) 0x30A5F7219E8E0B55,
                    (ulong) 0x2BEC3F65BCA57B6B, 0xDDD04969BAF1B75E,
                    0x99904CDBE394EA57, (ulong) 0x14B201D1E6EA40F6,
                    0xBBB0C08241284ADD, (ulong) 0x50F20463BF8F1DFF,
                    0xE8D7F93B93CBACB8, (ulong) 0x4D8CB68E477C86E8,
                    0xC1DD1B3992268E3F, (ulong) 0x7C5AA11209D62FCB,
                    (ulong) 0x2F3D98ABDB35C9AE, (ulong) 0x671369562BFD5FF5,
                    (ulong) 0x15C1E16C36CEE280, (ulong) 0x1D7EB2EDF8F39B17,
                    0xDA94D37DB00DFE01, 0x877BC3EC760B8ADA,
                    0xCB8495DFE153AE44, (ulong) 0x05A24773B7B410B3,
                    (ulong) 0x12857B783C32ABDF, 0x8EB770D06812513B,
                    (ulong) 0x536739B9D2E3E665, (ulong) 0x584D57E271B26468,
                    0xD789C78FC9849725, 0xA935BBFA7D1AE102,
                    0x8B1537A3DFA64188, 0xD0CD5D9BC378DE7A,
                    (ulong) 0x4AC82C9A4D80CFB7, (ulong) 0x42777F1B83BDB620,
                    (ulong) 0x72D2883A1D33BD75, (ulong) 0x5E7A2D4BAB6A8F41,
                    0xF4DAAB6BBB1C95D9, 0x905CFFE7FD8D31B6,
                    0x83AA6422119B381F, 0xC0AEFB8442022C49,
                    0xA0F908C663033AE3, 0xA428AF0804938826,
                    0xADE41C341A8A53C7, 0xAE7121EE77E6A85D,
                    0xC47F5C4A25929E8C, 0xB538E9AA55CDD863,
                    (ulong) 0x06377AA9DAD8EB29, 0xA18AE87BB3279895,
                    (ulong) 0x6EDFDA6A35E48414, (ulong) 0x6B7D9D19825094A7,
                    0xD41CFA55A4E86CBF, 0xE5CAEDC9EA42C59C,
                    0xA36C351C0E6FC179, (ulong) 0x5181E4DE6FABBF89,
                    0xFFF0C530184D17D4, 0x9D41EB1584045892,
                    (ulong) 0x1C0D525028D73961, 0xF178EC180CA8856A,
                    0x9A0571018EF811CD, (ulong) 0x4091A27C3EF5EFCC,
                    (ulong) 0x19AF15239F6329D2, (ulong) 0x347450EFF91EB990,
                    0xE11B4A078DD27759, 0xB9561DE5FC601331,
                    0x912F1F5A2DA993C0, (ulong) 0x1654DCB65BA2191A,
                    (ulong) 0x3E2DDE098A6B99EB, 0x8A66D71E0F82E3FE,
                    0x8C51ADB7D55A08D7, (ulong) 0x4533E50F8941FF7F,
                    (ulong) 0x02E6DD67BD4859EC, 0xE068AABA5DF6D52F,
                    0xC24826E3FF4A75A5, (ulong) 0x6C39070D88ACDDF8,
                    (ulong) 0x6486548C4691A46F, 0xD1BEBD26135C7C0C,
                    0xB30F93038F15334A, 0x82D9849FC1BF9A69,
                    0x9C320BA85420FAE4, 0xFA528243AFF90767,
                    0x9ED4D6CFE968A308, 0xB825FD582C44B147,
                    0x9B7691BC5EDCB3BB, 0xC7EA619048FE6516,
                    (ulong) 0x1063A61F817AF233, (ulong) 0x47D538683409A693,
                    (ulong) 0x63C2CE984C6DED30, (ulong) 0x2A9FDFD86C81D91D,
                    (ulong) 0x7B1E3B06032A6694, (ulong) 0x666089EBFBD9FD83,
                    (ulong) 0x0A598EE67375207B, (ulong) 0x07449A140AFC495F,
                    (ulong) 0x2CA8A571B6593234, (ulong) 0x1F986F8A45BBC2FB,
                    (ulong) 0x381AA4A050B372C2, (ulong) 0x5423A3ADD81FAF3A,
                    (ulong) 0x17273C0B8B86BB6C, 0xFE83258DC869B5A2,
                    (ulong) 0x287902BFD1C980F1, 0xF5A94BD66B3837AF,
                    0x88800A79B2CABA12, (ulong) 0x55504310083B0D4C,
                    0xDF36940E07B9EEB2, (ulong) 0x04D1A7CE6790B2C5,
                    (ulong) 0x612413FFF125B4DC, (ulong) 0x26F12B97C52C124F,
                    0x86082351A62F28AC, 0xEF93632F9937E5E7,
                    (ulong) 0x3507B052293A1BE6, 0xE72C30AE570A9C70,
                    0xD3586041AE1425E0, 0xDE4574B3D79D4CC4,
                    0x92BA228040C5685A, 0xF00B0CA5DC8C271C,
                    0xBE1287F1F69C5A6E, 0xF39E317FB1E0DC86,
                    (ulong) 0x495D114020EC342D, (ulong) 0x699B407E3F18CD4B,
                    0xDCA3A9D46AD51528, (ulong) 0x0D1D14F279896924,
                    (ulong) 0x0000000000000000, (ulong) 0x593EB75FA196C61E,
                    (ulong) 0x2E4E78160B116BD8, (ulong) 0x6D4AE7B058887F8E,
                    0xE65FD013872E3E06, (ulong) 0x7A6DDBBBD30EC4E2,
                    0xAC97FC89CAAEF1B1, (ulong) 0x09CCB33C1E19DBE1,
                    0x89F3EAC462EE1864, (ulong) 0x7770CF49AA87ADC6,
                    (ulong) 0x56C57ECA6557F6D6, (ulong) 0x03953DDA6D6CFB9A,
                    (ulong) 0x36928D884456E07C, (ulong) 0x1EEB8F37959F608D,
                    (ulong) 0x31D6179C4EAAA923, (ulong) 0x6FAC3AD7E5C02662,
                    (ulong) 0x43049FA653991456, 0xABD3669DC052B8EE,
                    0xAF02C153A7C20A2B, (ulong) 0x3CCB036E3723C007,
                    0x93C9C23D90E1CA2C, 0xC33BC65E2F6ED7D3,
                    (ulong) 0x4CFF56339758249E, 0xB1E94E64325D6AA6,
                    (ulong) 0x37E16D359472420A, (ulong) 0x79F8E661BE623F78,
                    (ulong) 0x5214D90402C74413, (ulong) 0x482EF1FDF0C8965B,
                    (ulong) 0x13F69BC5EC1609A9, (ulong) 0x0E88292814E592BE,
                    (ulong) 0x4E198B542A107D72, 0xCCC00FCBEBAFE71B,
                    (ulong) 0x1B49C844222B703E, (ulong) 0x2564164DA840E9D5,
                    (ulong) 0x20C6513E1FF4F966, 0xBAC3203F910CE8AB,
                    0xF2EDD1C261C47EF0, 0x814CB945ACD361F3,
                    0x95FEB8944A392105, (ulong) 0x5C9CF02C1622D6AD,
                    0x971865F3F77178E9, 0xBD87BA2B9BF0A1F4,
                    (ulong) 0x444005B259655D09, 0xED75BE48247FBC0B,
                    (ulong) 0x7596122E17CFF42A, 0xB44B091785E97A15,
                    0x966B854E2755DA9F, 0xEEE0839249134791,
                    (ulong) 0x32432A4623C652B9, 0xA8465B47AD3E4374,
                    0xF8B45F2412B15E8B, (ulong) 0x2417F6F078644BA3,
                    0xFB2162FE7FDDA511, (ulong) 0x4BBBCC279DA46DC1,
                    (ulong) 0x0173E0BDD024A276, (ulong) 0x22208C59A2BCA08A,
                    0x8FC4906DB836F34D, 0xE4B90D743A6667EA,
                    (ulong) 0x7147B5E0705F46EF, (ulong) 0x2782CB2A1508B039,
                    0xEC065EF5F45B1E7D, (ulong) 0x21B5B183CFD05B10,
                    0xDBE733C060295C77, 0x9FA73672394C017E,
                    0xCF55321186C31C81, 0xD8720E1A0D45A7ED,
                    (ulong) 0x3B8F997A3DDF8958, (ulong) 0x3AFC79C7EDFB2B2E,
                    0xE9A4198643EF0ECE, (ulong) 0x5F09CDF67B4E2D37,
                    (ulong) 0x4F6A6BE9FA34DF04, 0xB6ADD47038A123F9,
                    0x8D224D0A057EAAA1, 0xC96248B85C1BF7A8,
                    0xE3FD9760309A2EB5, (ulong) 0x0B2A6E5BA351820D,
                    0xEB42C4E1FEA75722, 0x948D58299A1D8373,
                    (ulong) 0x7FCF9CC864BAD451, 0xA55B4FB5D4B72A50,
                    (ulong) 0x08BF5381CE3D7997, (ulong) 0x46A6D8D5E42D04E5,
                    0xD22B80FC7E308796, (ulong) 0x57B69E77B57354A0,
                    (ulong) 0x3969441D8097D0B4, (ulong) 0x3330CAFBF3E2F0CF,
                    0xE28E77DDE0BE8CC3, (ulong) 0x62B12E259C494F46,
                    0xA6CE726FB9DBD1CA, (ulong) 0x41E242C1EED14DBA,
                    (ulong) 0x76032FF47AA30FB0
                },
                new[]
                {
                    (ulong) 0x45B268A93ACDE4CC,
                    0xAF7F0BE884549D08, (ulong) 0x048354B3C1468263,
                    0x925435C2C80EFED2, 0xEE4E37F27FDFFBA7,
                    (ulong) 0x167A33920C60F14D, 0xFB123B52EA03E584,
                    (ulong) 0x4A0CAB53FDBB9007, 0x9DEAF6380F788A19,
                    0xCB48EC558F0CB32A, 0xB59DC4B2D6FEF7E0,
                    0xDCDBCA22F4F3ECB6, (ulong) 0x11DF5813549A9C40,
                    0xE33FDEDF568ACED3, 0xA0C1C8124322E9C3,
                    (ulong) 0x07A56B8158FA6D0D, (ulong) 0x77279579B1E1F3DD,
                    0xD9B18B74422AC004, 0xB8EC2D9FFFABC294,
                    0xF4ACF8A82D75914F, (ulong) 0x7BBF69B1EF2B6878,
                    0xC4F62FAF487AC7E1, (ulong) 0x76CE809CC67E5D0C,
                    (ulong) 0x6711D88F92E4C14C, (ulong) 0x627B99D9243DEDFE,
                    (ulong) 0x234AA5C3DFB68B51, 0x909B1F15262DBF6D,
                    (ulong) 0x4F66EA054B62BCB5, (ulong) 0x1AE2CF5A52AA6AE8,
                    0xBEA053FBD0CE0148, 0xED6808C0E66314C9,
                    (ulong) 0x43FE16CD15A82710, 0xCD049231A06970F6,
                    0xE7BC8A6C97CC4CB0, (ulong) 0x337CE835FCB3B9C0,
                    (ulong) 0x65DEF2587CC780F3, (ulong) 0x52214EDE4132BB50,
                    0x95F15E4390F493DF, 0x870839625DD2E0F1,
                    (ulong) 0x41313C1AFB8B66AF, 0x91720AF051B211BC,
                    (ulong) 0x477D427ED4EEA573, (ulong) 0x2E3B4CEEF6E3BE25,
                    0x82627834EB0BCC43, 0x9C03E3DD78E724C8,
                    (ulong) 0x2877328AD9867DF9, (ulong) 0x14B51945E243B0F2,
                    (ulong) 0x574B0F88F7EB97E2, 0x88B6FA989AA4943A,
                    (ulong) 0x19C4F068CB168586, (ulong) 0x50EE6409AF11FAEF,
                    (ulong) 0x7DF317D5C04EABA4, (ulong) 0x7A567C5498B4C6A9,
                    0xB6BBFB804F42188E, (ulong) 0x3CC22BCF3BC5CD0B,
                    0xD04336EAAA397713, 0xF02FAC1BEC33132C,
                    (ulong) 0x2506DBA7F0D3488D, 0xD7E65D6BF2C31A1E,
                    (ulong) 0x5EB9B2161FF820F5, 0x842E0650C46E0F9F,
                    (ulong) 0x716BEB1D9E843001, 0xA933758CAB315ED4,
                    (ulong) 0x3FE414FDA2792265, (ulong) 0x27C9F1701EF00932,
                    (ulong) 0x73A4C1CA70A771BE, 0x94184BA6E76B3D0E,
                    (ulong) 0x40D829FF8C14C87E, (ulong) 0x0FBEC3FAC77674CB,
                    (ulong) 0x3616A9634A6A9572, 0x8F139119C25EF937,
                    0xF545ED4D5AEA3F9E, 0xE802499650BA387B,
                    (ulong) 0x6437E7BD0B582E22, 0xE6559F89E053E261,
                    0x80AD52E305288DFC, (ulong) 0x6DC55A23E34B9935,
                    0xDE14E0F51AD0AD09, 0xC6390578A659865E,
                    0x96D7617109487CB1, 0xE2D6CB3A21156002,
                    (ulong) 0x01E915E5779FAED1, 0xADB0213F6A77DCB7,
                    0x9880B76EB9A1A6AB, (ulong) 0x5D9F8D248644CF9B,
                    0xFD5E4536C5662658, 0xF1C6B9FE9BACBDFD,
                    0xEACD6341BE9979C4, 0xEFA7221708405576,
                    (ulong) 0x510771ECD88E543E, 0xC2BA51CB671F043D,
                    (ulong) 0x0AD482AC71AF5879, 0xFE787A045CDAC936,
                    0xB238AF338E049AED, 0xBD866CC94972EE26,
                    (ulong) 0x615DA6EBBD810290, (ulong) 0x3295FDD08B2C1711,
                    0xF834046073BF0AEA, 0xF3099329758FFC42,
                    (ulong) 0x1CAEB13E7DCFA934, 0xBA2307481188832B,
                    (ulong) 0x24EFCE42874CE65C, (ulong) 0x0E57D61FB0E9DA1A,
                    0xB3D1BAD6F99B343C, 0xC0757B1C893C4582,
                    (ulong) 0x2B510DB8403A9297, (ulong) 0x5C7698C1F1DB614A,
                    (ulong) 0x3E0D0118D5E68CB4, 0xD60F488E855CB4CF,
                    0xAE961E0DF3CB33D9, (ulong) 0x3A8E55AB14A00ED7,
                    (ulong) 0x42170328623789C1, 0x838B6DD19C946292,
                    0x895FEF7DED3B3AEB, 0xCFCBB8E64E4A3149,
                    (ulong) 0x064C7E642F65C3DC, (ulong) 0x3D2B3E2A4C5A63DA,
                    (ulong) 0x5BD3F340A9210C47, 0xB474D157A1615931,
                    0xAC5934DA1DE87266, (ulong) 0x6EE365117AF7765B,
                    0xC86ED36716B05C44, 0x9BA6885C201D49C5,
                    0xB905387A88346C45, (ulong) 0x131072C4BAB9DDFF,
                    0xBF49461EA751AF99, 0xD52977BC1CE05BA1,
                    0xB0F785E46027DB52, (ulong) 0x546D30BA6E57788C,
                    (ulong) 0x305AD707650F56AE, 0xC987C682612FF295,
                    0xA5AB8944F5FBC571, (ulong) 0x7ED528E759F244CA,
                    0x8DDCBBCE2C7DB888, 0xAA154ABE328DB1BA,
                    (ulong) 0x1E619BE993ECE88B, (ulong) 0x09F2BD9EE813B717,
                    (ulong) 0x7401AA4B285D1CB3, (ulong) 0x21858F143195CAEE,
                    (ulong) 0x48C381841398D1B8, 0xFCB750D3B2F98889,
                    (ulong) 0x39A86A998D1CE1B9, (ulong) 0x1F888E0CE473465A,
                    (ulong) 0x7899568376978716, (ulong) 0x02CF2AD7EE2341BF,
                    0x85C713B5B3F1A14E, 0xFF916FE12B4567E7,
                    (ulong) 0x7C1A0230B7D10575, (ulong) 0x0C98FCC85ECA9BA5,
                    0xA3E7F720DA9E06AD, (ulong) 0x6A6031A2BBB1F438,
                    0x973E74947ED7D260, (ulong) 0x2CF4663918C0FF9A,
                    (ulong) 0x5F50A7F368678E24, (ulong) 0x34D983B4A449D4CD,
                    (ulong) 0x68AF1B755592B587, (ulong) 0x7F3C3D022E6DEA1B,
                    0xABFC5F5B45121F6B, (ulong) 0x0D71E92D29553574,
                    0xDFFDF5106D4F03D8, (ulong) 0x081BA87B9F8C19C6,
                    0xDB7EA1A3AC0981BB, 0xBBCA12AD66172DFA,
                    (ulong) 0x79704366010829C7, (ulong) 0x179326777BFF5F9C,
                    (ulong) 0x0000000000000000, 0xEB2476A4C906D715,
                    (ulong) 0x724DD42F0738DF6F, 0xB752EE6538DDB65F,
                    (ulong) 0x37FFBC863DF53BA3, 0x8EFA84FCB5C157E6,
                    0xE9EB5C73272596AA, (ulong) 0x1B0BDABF2535C439,
                    0x86E12C872A4D4E20, 0x9969A28BCE3E087A,
                    0xFAFB2EB79D9C4B55, (ulong) 0x056A4156B6D92CB2,
                    (ulong) 0x5A3AE6A5DEBEA296, (ulong) 0x22A3B026A8292580,
                    (ulong) 0x53C85B3B36AD1581, 0xB11E900117B87583,
                    0xC51F3A4A3FE56930, 0xE019E1EDCF3621BD,
                    0xEC811D2591FCBA18, (ulong) 0x445B7D4C4D524A1D,
                    0xA8DA6069DCAEF005, (ulong) 0x58F5CC72309DE329,
                    0xD4C062596B7FF570, 0xCE22AD0339D59F98,
                    (ulong) 0x591CD99747024DF8, 0x8B90C5AA03187B54,
                    0xF663D27FC356D0F0, 0xD8589E9135B56ED5,
                    (ulong) 0x35309651D3D67A1C, (ulong) 0x12F96721CD26732E,
                    0xD28C1C3D441A36AC, (ulong) 0x492A946164077F69,
                    (ulong) 0x2D1D73DC6F5F514B, (ulong) 0x6F0A70F40D68D88A,
                    (ulong) 0x60B4B30ECA1EAC41, 0xD36509D83385987D,
                    (ulong) 0x0B3D97490630F6A8, 0x9ECCC90A96C46577,
                    0xA20EE2C5AD01A87C, 0xE49AB55E0E70A3DE,
                    0xA4429CA182646BA0, 0xDA97B446DB962F6A,
                    0xCCED87D4D7F6DE27, (ulong) 0x2AB8185D37A53C46,
                    0x9F25DCEFE15BCBA6, 0xC19C6EF9FEA3EB53,
                    0xA764A3931BD884CE, (ulong) 0x2FD2590B817C10F4,
                    (ulong) 0x56A21A6D80743933, 0xE573A0BB79EF0D0F,
                    (ulong) 0x155C0CA095DC1E23, (ulong) 0x6C2C4FC694D437E4,
                    (ulong) 0x10364DF623053291, 0xDD32DFC7836C4267,
                    (ulong) 0x03263F3299BCEF6E, (ulong) 0x66F8CD6AE57B6F9D,
                    0x8C35AE2B5BE21659, (ulong) 0x31B3C2E21290F87F,
                    0x93BD2027BF915003, (ulong) 0x69460E90220D1B56,
                    (ulong) 0x299E276FAE19D328, (ulong) 0x63928C3C53A2432F,
                    (ulong) 0x7082FEF8E91B9ED0, 0xBC6F792C3EED40F7,
                    (ulong) 0x4C40D537D2DE53DB, (ulong) 0x75E8BFAE5FC2B262,
                    (ulong) 0x4DA9C0D2A541FD0A, (ulong) 0x4E8FFFE03CFD1264,
                    (ulong) 0x2620E495696FA7E3, 0xE1F0F408B8A98F6C,
                    0xD1AA230FDDA6D9C2, 0xC7D0109DD1C6288F,
                    0x8A79D04F7487D585, (ulong) 0x4694579BA3710BA2,
                    (ulong) 0x38417F7CFA834F68, (ulong) 0x1D47A4DB0A5007E5,
                    (ulong) 0x206C9AF1460A643F, 0xA128DDF734BD4712,
                    0x8144470672B7232D, 0xF2E086CC02105293,
                    (ulong) 0x182DE58DBC892B57, 0xCAA1F9B0F8931DFB,
                    (ulong) 0x6B892447CC2E5AE9, 0xF9DD11850420A43B,
                    (ulong) 0x4BE5BEB68A243ED6, (ulong) 0x5584255F19C8D65D,
                    (ulong) 0x3B67404E633FA006, 0xA68DB6766C472A1F,
                    0xF78AC79AB4C97E21, 0xC353442E1080AAEC,
                    0x9A4F9DB95782E714
                },
                new[]
                {
                    (ulong) 0x05BA7BC82C9B3220,
                    (ulong) 0x31A54665F8B65E4F, 0xB1B651F77547F4D4,
                    0x8BFA0D857BA46682, 0x85A96C5AA16A98BB,
                    0x990FAEF908EB79C9, 0xA15E37A247F4A62D,
                    (ulong) 0x76857DCD5D27741E, 0xF8C50B800A1820BC,
                    0xBE65DCB201F7A2B4, (ulong) 0x666D1B986F9426E7,
                    (ulong) 0x4CC921BF53C4E648, 0x95410A0F93D9CA42,
                    (ulong) 0x20CDCCAA647BA4EF, (ulong) 0x429A4060890A1871,
                    (ulong) 0x0C4EA4F69B32B38B, 0xCCDA362DDE354CD3,
                    0x96DC23BC7C5B2FA9, 0xC309BB68AA851AB3,
                    0xD26131A73648E013, (ulong) 0x021DC52941FC4DB2,
                    0xCD5ADAB7704BE48A, 0xA77965D984ED71E6,
                    (ulong) 0x32386FD61734BBA4, 0xE82D6DD538AB7245,
                    (ulong) 0x5C2147EA6177B4B1, (ulong) 0x5DA1AB70CF091CE8,
                    0xAC907FCE72B8BDFF, (ulong) 0x57C85DFD972278A8,
                    0xA4E44C6A6B6F940D, (ulong) 0x3851995B4F1FDFE4,
                    (ulong) 0x62578CCAED71BC9E, 0xD9882BB0C01D2C0A,
                    0x917B9D5D113C503B, 0xA2C31E11A87643C6,
                    0xE463C923A399C1CE, 0xF71686C57EA876DC,
                    0x87B4A973E096D509, 0xAF0D567D9D3A5814,
                    0xB40C2A3F59DCC6F4, (ulong) 0x3602F88495D121DD,
                    0xD3E1DD3D9836484A, 0xF945E71AA46688E5,
                    (ulong) 0x7518547EB2A591F5, 0x9366587450C01D89,
                    0x9EA81018658C065B, (ulong) 0x4F54080CBC4603A3,
                    (ulong) 0x2D0384C65137BF3D, 0xDC325078EC861E2A,
                    0xEA30A8FC79573FF7, (ulong) 0x214D2030CA050CB6,
                    (ulong) 0x65F0322B8016C30C, (ulong) 0x69BE96DD1B247087,
                    0xDB95EE9981E161B8, 0xD1FC1814D9CA05F8,
                    0x820ED2BBCC0DE729, (ulong) 0x63D76050430F14C7,
                    (ulong) 0x3BCCB0E8A09D3A0F, 0x8E40764D573F54A2,
                    (ulong) 0x39D175C1E16177BD, (ulong) 0x12F5A37C734F1F4B,
                    0xAB37C12F1FDFC26D, (ulong) 0x5648B167395CD0F1,
                    (ulong) 0x6C04ED1537BF42A7, 0xED97161D14304065,
                    (ulong) 0x7D6C67DAAB72B807, 0xEC17FA87BA4EE83C,
                    0xDFAF79CB0304FBC1, (ulong) 0x733F060571BC463E,
                    (ulong) 0x78D61C1287E98A27, 0xD07CF48E77B4ADA1,
                    0xB9C262536C90DD26, 0xE2449B5860801605,
                    0x8FC09AD7F941FCFB, 0xFAD8CEA94BE46D0E,
                    0xA343F28B0608EB9F, 0x9B126BD04917347B,
                    0x9A92874AE7699C22, (ulong) 0x1B017C42C4E69EE0,
                    (ulong) 0x3A4C5C720EE39256, (ulong) 0x4B6E9F5E3EA399DA,
                    (ulong) 0x6BA353F45AD83D35, 0xE7FEE0904C1B2425,
                    (ulong) 0x22D009832587E95D, 0x842980C00F1430E2,
                    0xC6B3C0A0861E2893, (ulong) 0x087433A419D729F2,
                    (ulong) 0x341F3DADD42D6C6F, 0xEE0A3FAEFBB2A58E,
                    (ulong) 0x4AEE73C490DD3183, 0xAAB72DB5B1A16A34,
                    0xA92A04065E238FDF, (ulong) 0x7B4B35A1686B6FCC,
                    (ulong) 0x6A23BF6EF4A6956C, (ulong) 0x191CB96B851AD352,
                    (ulong) 0x55D598D4D6DE351A, 0xC9604DE5F2AE7EF3,
                    (ulong) 0x1CA6C2A3A981E172, 0xDE2F9551AD7A5398,
                    (ulong) 0x3025AAFF56C8F616, (ulong) 0x15521D9D1E2860D9,
                    (ulong) 0x506FE31CFA45073A, (ulong) 0x189C55F12B647B0B,
                    (ulong) 0x0180EC9AAE7EA859, (ulong) 0x7CEC8B40050C105E,
                    (ulong) 0x2350E5198BF94104, 0xEF8AD33455CC0DD7,
                    (ulong) 0x07A7BEE16D677F92, 0xE5E325B90DE76997,
                    (ulong) 0x5A061591A26E637A, 0xB611EF1618208B46,
                    (ulong) 0x09F4DF3EB7A981AB, (ulong) 0x1EBB078AE87DACC0,
                    0xB791038CB65E231F, (ulong) 0x0FD38D4574B05660,
                    (ulong) 0x67EDF702C1EA8EBE, 0xBA5F4BE0831238CD,
                    0xE3C477C2CEFEBE5C, (ulong) 0x0DCE486C354C1BD2,
                    0x8C5DB36416C31910, (ulong) 0x26EA9ED1A7627324,
                    (ulong) 0x039D29B3EF82E5EB, 0x9F28FC82CBF2AE02,
                    0xA8AAE89CF05D2786, (ulong) 0x431AACFA2774B028,
                    0xCF471F9E31B7A938, (ulong) 0x581BD0B8E3922EC8,
                    0xBC78199B400BEF06, 0x90FB71C7BF42F862,
                    (ulong) 0x1F3BEB1046030499, (ulong) 0x683E7A47B55AD8DE,
                    0x988F4263A695D190, 0xD808C72A6E638453,
                    (ulong) 0x0627527BC319D7CB, 0xEBB04466D72997AE,
                    0xE67E0C0AE2658C7C, (ulong) 0x14D2F107B056C880,
                    (ulong) 0x7122C32C30400B8C, 0x8A7AE11FD5DACEDB,
                    0xA0DEDB38E98A0E74, 0xAD109354DCC615A6,
                    (ulong) 0x0BE91A17F655CC19, 0x8DDD5FFEB8BDB149,
                    0xBFE53028AF890AED, 0xD65BA6F5B4AD7A6A,
                    (ulong) 0x7956F0882997227E, (ulong) 0x10E8665532B352F9,
                    (ulong) 0x0E5361DFDACEFE39, 0xCEC7F3049FC90161,
                    0xFF62B561677F5F2E, 0x975CCF26D22587F0,
                    (ulong) 0x51EF0F86543BAF63, (ulong) 0x2F1E41EF10CBF28F,
                    (ulong) 0x52722635BBB94A88, 0xAE8DBAE73344F04D,
                    (ulong) 0x410769D36688FD9A, 0xB3AB94DE34BBB966,
                    0x801317928DF1AA9B, 0xA564A0F0C5113C54,
                    0xF131D4BEBDB1A117, (ulong) 0x7F71A2F3EA8EF5B5,
                    (ulong) 0x40878549C8F655C3, (ulong) 0x7EF14E6944F05DEC,
                    0xD44663DCF55137D8, 0xF2ACFD0D523344FC,
                    (ulong) 0x0000000000000000, (ulong) 0x5FBC6E598EF5515A,
                    (ulong) 0x16CF342EF1AA8532, 0xB036BD6DDB395C8D,
                    (ulong) 0x13754FE6DD31B712, 0xBBDFA77A2D6C9094,
                    0x89E7C8AC3A582B30, (ulong) 0x3C6B0E09CDFA459D,
                    0xC4AE0589C7E26521, (ulong) 0x49735A777F5FD468,
                    0xCAFD64561D2C9B18, 0xDA1502032F9FC9E1,
                    0x8867243694268369, (ulong) 0x3782141E3BAF8984,
                    0x9CB5D53124704BE9, 0xD7DB4A6F1AD3D233,
                    0xA6F989432A93D9BF, 0x9D3539AB8A0EE3B0,
                    (ulong) 0x53F2CAAF15C7E2D1, (ulong) 0x6E19283C76430F15,
                    (ulong) 0x3DEBE2936384EDC4, (ulong) 0x5E3C82C3208BF903,
                    (ulong) 0x33B8834CB94A13FD, (ulong) 0x6470DEB12E686B55,
                    (ulong) 0x359FD1377A53C436, (ulong) 0x61CAA57902F35975,
                    (ulong) 0x043A975282E59A79, 0xFD7F70482683129C,
                    0xC52EE913699CCD78, (ulong) 0x28B9FF0E7DAC8D1D,
                    (ulong) 0x5455744E78A09D43, 0xCB7D88CCB3523341,
                    (ulong) 0x44BD121B4A13CFBA, (ulong) 0x4D49CD25FDBA4E11,
                    (ulong) 0x3E76CB208C06082F, (ulong) 0x3FF627BA2278A076,
                    0xC28957F204FBB2EA, (ulong) 0x453DFE81E46D67E3,
                    0x94C1E6953DA7621B, (ulong) 0x2C83685CFF491764,
                    0xF32C1197FC4DECA5, (ulong) 0x2B24D6BD922E68F6,
                    0xB22B78449AC5113F, (ulong) 0x48F3B6EDD1217C31,
                    (ulong) 0x2E9EAD75BEB55AD6, (ulong) 0x174FD8B45FD42D6B,
                    (ulong) 0x4ED4E4961238ABFA, 0x92E6B4EEFEBEB5D0,
                    (ulong) 0x46A0D7320BEF8208, (ulong) 0x47203BA8A5912A51,
                    (ulong) 0x24F75BF8E69E3E96, 0xF0B1382413CF094E,
                    0xFEE259FBC901F777, (ulong) 0x276A724B091CDB7D,
                    0xBDF8F501EE75475F, (ulong) 0x599B3C224DEC8691,
                    (ulong) 0x6D84018F99C1EAFE, (ulong) 0x7498B8E41CDB39AC,
                    0xE0595E71217C5BB7, (ulong) 0x2AA43A273C50C0AF,
                    0xF50B43EC3F543B6E, 0x838E3E2162734F70,
                    0xC09492DB4507FF58, (ulong) 0x72BFEA9FDFC2EE67,
                    (ulong) 0x11688ACF9CCDFAA0, (ulong) 0x1A8190D86A9836B9,
                    (ulong) 0x7ACBD93BC615C795, 0xC7332C3A286080CA,
                    0x863445E94EE87D50, 0xF6966A5FD0D6DE85,
                    0xE9AD814F96D5DA1C, (ulong) 0x70A22FB69E3EA3D5,
                    (ulong) 0x0A69F68D582B6440, 0xB8428EC9C2EE757F,
                    (ulong) 0x604A49E3AC8DF12C, (ulong) 0x5B86F90B0C10CB23,
                    0xE1D9B2EB8F02F3EE, (ulong) 0x29391394D3D22544,
                    0xC8E0A17F5CD0D6AA, 0xB58CC6A5F7A26EAD,
                    0x8193FB08238F02C2, 0xD5C68F465B2F9F81,
                    0xFCFF9CD288FDBAC5, (ulong) 0x77059157F359DC47,
                    (ulong) 0x1D262E3907FF492B, 0xFB582233E59AC557,
                    0xDDB2BCE242F8B673, (ulong) 0x2577B76248E096CF,
                    (ulong) 0x6F99C4A6D83DA74C, 0xC1147E41EB795701,
                    0xF48BAF76912A9337
                },
                new[]
                {
                    (ulong) 0x3EF29D249B2C0A19,
                    0xE9E16322B6F8622F, (ulong) 0x5536994047757F7A,
                    0x9F4D56D5A47B0B33, 0x822567466AA1174C,
                    0xB8F5057DEB082FB2, 0xCC48C10BF4475F53,
                    (ulong) 0x373088D4275DEC3A, 0x968F4325180AED10,
                    (ulong) 0x173D232CF7016151, 0xAE4ED09F946FCC13,
                    0xFD4B4741C4539873, (ulong) 0x1B5B3F0DD9933765,
                    (ulong) 0x2FFCB0967B644052, 0xE02376D20A89840C,
                    0xA3AE3A70329B18D7, (ulong) 0x419CBD2335DE8526,
                    0xFAFEBF115B7C3199, (ulong) 0x0397074F85AA9B0D,
                    0xC58AD4FB4836B970, 0xBEC60BE3FC4104A8,
                    (ulong) 0x1EFF36DC4B708772, (ulong) 0x131FDC33ED8453B6,
                    (ulong) 0x0844E33E341764D3, (ulong) 0x0FF11B6EAB38CD39,
                    (ulong) 0x64351F0A7761B85A, (ulong) 0x3B5694F509CFBA0E,
                    (ulong) 0x30857084B87245D0, (ulong) 0x47AFB3BD2297AE3C,
                    0xF2BA5C2F6F6B554A, (ulong) 0x74BDC4761F4F70E1,
                    0xCFDFC64471EDC45E, 0xE610784C1DC0AF16,
                    (ulong) 0x7ACA29D63C113F28, (ulong) 0x2DED411776A859AF,
                    0xAC5F211E99A3D5EE, 0xD484F949A87EF33B,
                    (ulong) 0x3CE36CA596E013E4, 0xD120F0983A9D432C,
                    (ulong) 0x6BC40464DC597563, (ulong) 0x69D5F5E5D1956C9E,
                    0x9AE95F043698BB24, 0xC9ECC8DA66A4EF44,
                    0xD69508C8A5B2EAC6, 0xC40C2235C0503B80,
                    (ulong) 0x38C193BA8C652103, (ulong) 0x1CEEC75D46BC9E8F,
                    0xD331011937515AD1, 0xD8E2E56886ECA50F,
                    0xB137108D5779C991, (ulong) 0x709F3B6905CA4206,
                    (ulong) 0x4FEB50831680CAEF, 0xEC456AF3241BD238,
                    (ulong) 0x58D673AFE181ABBE, (ulong) 0x242F54E7CAD9BF8C,
                    (ulong) 0x0211F1810DCC19FD, 0x90BC4DBB0F43C60A,
                    0x9518446A9DA0761D, 0xA1BFCBF13F57012A,
                    (ulong) 0x2BDE4F8961E172B5, (ulong) 0x27B853A84F732481,
                    0xB0B1E643DF1F4B61, (ulong) 0x18CC38425C39AC68,
                    0xD2B7F7D7BF37D821, (ulong) 0x3103864A3014C720,
                    (ulong) 0x14AA246372ABFA5C, (ulong) 0x6E600DB54EBAC574,
                    (ulong) 0x394765740403A3F3, (ulong) 0x09C215F0BC71E623,
                    (ulong) 0x2A58B947E987F045, (ulong) 0x7B4CDF18B477BDD8,
                    0x9709B5EB906C6FE0, (ulong) 0x73083C268060D90B,
                    0xFEDC400E41F9037E, (ulong) 0x284948C6E44BE9B8,
                    (ulong) 0x728ECAE808065BFB, (ulong) 0x06330E9E17492B1A,
                    (ulong) 0x5950856169E7294E, 0xBAE4F4FCE6C4364F,
                    0xCA7BCF95E30E7449, (ulong) 0x7D7FD186A33E96C2,
                    (ulong) 0x52836110D85AD690, (ulong) 0x4DFAA1021B4CD312,
                    0x913ABB75872544FA, 0xDD46ECB9140F1518,
                    (ulong) 0x3D659A6B1E869114, 0xC23F2CABD719109A,
                    0xD713FE062DD46836, 0xD0A60656B2FBC1DC,
                    (ulong) 0x221C5A79DD909496, 0xEFD26DBCA1B14935,
                    (ulong) 0x0E77EDA0235E4FC9, 0xCBFD395B6B68F6B9,
                    (ulong) 0x0DE0EAEFA6F4D4C4, (ulong) 0x0422FF1F1A8532E7,
                    0xF969B85EDED6AA94, (ulong) 0x7F6E2007AEF28F3F,
                    (ulong) 0x3AD0623B81A938FE, (ulong) 0x6624EE8B7AADA1A7,
                    0xB682E8DDC856607B, 0xA78CC56F281E2A30,
                    0xC79B257A45FAA08D, (ulong) 0x5B4174E0642B30B3,
                    (ulong) 0x5F638BFF7EAE0254, (ulong) 0x4BC9AF9C0C05F808,
                    0xCE59308AF98B46AE, 0x8FC58DA9CC55C388,
                    0x803496C7676D0EB1, 0xF33CAAE1E70DD7BA,
                    0xBB6202326EA2B4BF, 0xD5020F87201871CB,
                    0x9D5CA754A9B712CE, 0x841669D87DE83C56,
                    0x8A6184785EB6739F, (ulong) 0x420BBA6CB0741E2B,
                    0xF12D5B60EAC1CE47, (ulong) 0x76AC35F71283691C,
                    (ulong) 0x2C6BB7D9FECEDB5F, 0xFCCDB18F4C351A83,
                    (ulong) 0x1F79C012C3160582, 0xF0ABADAE62A74CB7,
                    0xE1A5801C82EF06FC, (ulong) 0x67A21845F2CB2357,
                    (ulong) 0x5114665F5DF04D9D, 0xBF40FD2D74278658,
                    0xA0393D3FB73183DA, (ulong) 0x05A409D192E3B017,
                    0xA9FB28CF0B4065F9, (ulong) 0x25A9A22942BF3D7C,
                    0xDB75E22703463E02, 0xB326E10C5AB5D06C,
                    0xE7968E8295A62DE6, 0xB973F3B3636EAD42,
                    0xDF571D3819C30CE5, 0xEE549B7229D7CBC5,
                    (ulong) 0x12992AFD65E2D146, 0xF8EF4E9056B02864,
                    0xB7041E134030E28B, 0xC02EDD2ADAD50967,
                    0x932B4AF48AE95D07, (ulong) 0x6FE6FB7BC6DC4784,
                    (ulong) 0x239AACB755F61666, (ulong) 0x401A4BEDBDB807D6,
                    (ulong) 0x485EA8D389AF6305, 0xA41BC220ADB4B13D,
                    (ulong) 0x753B32B89729F211, 0x997E584BB3322029,
                    (ulong) 0x1D683193CEDA1C7F, 0xFF5AB6C0C99F818E,
                    (ulong) 0x16BBD5E27F67E3A1, 0xA59D34EE25D233CD,
                    0x98F8AE853B54A2D9, (ulong) 0x6DF70AFACB105E79,
                    (ulong) 0x795D2E99B9BBA425, 0x8E437B6744334178,
                    (ulong) 0x0186F6CE886682F0, 0xEBF092A3BB347BD2,
                    0xBCD7FA62F18D1D55, 0xADD9D7D011C5571E,
                    (ulong) 0x0BD3E471B1BDFFDE, 0xAA6C2F808EEAFEF4,
                    (ulong) 0x5EE57D31F6C880A4, 0xF50FA47FF044FCA0,
                    (ulong) 0x1ADDC9C351F5B595, 0xEA76646D3352F922,
                    (ulong) 0x0000000000000000, 0x85909F16F58EBEA6,
                    (ulong) 0x46294573AAF12CCC, (ulong) 0x0A5512BF39DB7D2E,
                    (ulong) 0x78DBD85731DD26D5, (ulong) 0x29CFBE086C2D6B48,
                    (ulong) 0x218B5D36583A0F9B, (ulong) 0x152CD2ADFACD78AC,
                    0x83A39188E2C795BC, 0xC3B9DA655F7F926A,
                    0x9ECBA01B2C1D89C3, (ulong) 0x07B5F8509F2FA9EA,
                    (ulong) 0x7EE8D6C926940DCF, (ulong) 0x36B67E1AAF3B6ECA,
                    0x86079859702425AB, 0xFB7849DFD31AB369,
                    (ulong) 0x4C7C57CC932A51E2, 0xD96413A60E8A27FF,
                    (ulong) 0x263EA566C715A671, (ulong) 0x6C71FC344376DC89,
                    (ulong) 0x4A4F595284637AF8, 0xDAF314E98B20BCF2,
                    (ulong) 0x572768C14AB96687, (ulong) 0x1088DB7C682EC8BB,
                    0x887075F9537A6A62, (ulong) 0x2E7A4658F302C2A2,
                    (ulong) 0x619116DBE582084D, 0xA87DDE018326E709,
                    0xDCC01A779C6997E8, 0xEDC39C3DAC7D50C8,
                    0xA60A33A1A078A8C0, 0xC1A82BE452B38B97,
                    (ulong) 0x3F746BEA134A88E9, 0xA228CCBEBAFD9A27,
                    0xABEAD94E068C7C04, 0xF48952B178227E50,
                    (ulong) 0x5CF48CB0FB049959, (ulong) 0x6017E0156DE48ABD,
                    (ulong) 0x4438B4F2A73D3531, 0x8C528AE649FF5885,
                    0xB515EF924DFCFB76, (ulong) 0x0C661C212E925634,
                    0xB493195CC59A7986, 0x9CDA519A21D1903E,
                    (ulong) 0x32948105B5BE5C2D, (ulong) 0x194ACE8CD45F2E98,
                    (ulong) 0x438D4CA238129CDB, 0x9B6FA9CABEFE39D4,
                    0x81B26009EF0B8C41, 0xDED1EBF691A58E15,
                    (ulong) 0x4E6DA64D9EE6481F, (ulong) 0x54B06F8ECF13FD8A,
                    (ulong) 0x49D85E1D01C9E1F5, 0xAFC826511C094EE3,
                    0xF698A33075EE67AD, (ulong) 0x5AC7822EEC4DB243,
                    0x8DD47C28C199DA75, 0x89F68337DB1CE892,
                    0xCDCE37C57C21DDA3, (ulong) 0x530597DE503C5460,
                    (ulong) 0x6A42F2AA543FF793, (ulong) 0x5D727A7E73621BA9,
                    0xE232875307459DF1, (ulong) 0x56A19E0FC2DFE477,
                    0xC61DD3B4CD9C227D, 0xE5877F03986A341B,
                    0x949EB2A415C6F4ED, (ulong) 0x6206119460289340,
                    (ulong) 0x6380E75AE84E11B0, 0x8BE772B6D6D0F16F,
                    (ulong) 0x50929091D596CF6D, 0xE86795EC3E9EE0DF,
                    (ulong) 0x7CF927482B581432, 0xC86A3E14EEC26DB4,
                    (ulong) 0x7119CDA78DACC0F6, 0xE40189CD100CB6EB,
                    0x92ADBC3A028FDFF7, 0xB2A017C2D2D3529C,
                    (ulong) 0x200DABF8D05C8D6B, (ulong) 0x34A78F9BA2F77737,
                    0xE3B4719D8F231F01, (ulong) 0x45BE423C2F5BB7C1,
                    0xF71E55FEFD88E55D, (ulong) 0x6853032B59F3EE6E,
                    (ulong) 0x65B3E9C4FF073AAA, (ulong) 0x772AC3399AE5EBEC,
                    0x87816E97F842A75B, (ulong) 0x110E2DB2E0484A4B,
                    (ulong) 0x331277CB3DD8DEDD, 0xBD510CAC79EB9FA5,
                    (ulong) 0x352179552A91F5C7
                },
                new[]
                {
                    0x8AB0A96846E06A6D,
                    (ulong) 0x43C7E80B4BF0B33A, (ulong) 0x08C9B3546B161EE5,
                    (ulong) 0x39F1C235EBA990BE, 0xC1BEF2376606C7B2,
                    (ulong) 0x2C209233614569AA, 0xEB01523B6FC3289A,
                    0x946953AB935ACEDD, (ulong) 0x272838F63E13340E,
                    0x8B0455ECA12BA052, (ulong) 0x77A1B2C4978FF8A2,
                    0xA55122CA13E54086, (ulong) 0x2276135862D3F1CD,
                    0xDB8DDFDE08B76CFE, (ulong) 0x5D1E12C89E4A178A,
                    (ulong) 0x0E56816B03969867, 0xEE5F79953303ED59,
                    0xAFED748BAB78D71D, (ulong) 0x6D929F2DF93E53EE,
                    0xF5D8A8F8BA798C2A, 0xF619B1698E39CF6B,
                    0x95DDAF2F749104E2, 0xEC2A9C80E0886427,
                    0xCE5C8FD8825B95EA, 0xC4E0D9993AC60271,
                    (ulong) 0x4699C3A5173076F9, (ulong) 0x3D1B151F50A29F42,
                    0x9ED505EA2BC75946, (ulong) 0x34665ACFDC7F4B98,
                    (ulong) 0x61B1FB53292342F7, 0xC721C0080E864130,
                    0x8693CD1696FD7B74, 0x872731927136B14B,
                    0xD3446C8A63A1721B, (ulong) 0x669A35E8A6680E4A,
                    0xCAB658F239509A16, 0xA4E5DE4EF42E8AB9,
                    (ulong) 0x37A7435EE83F08D9, (ulong) 0x134E6239E26C7F96,
                    0x82791A3C2DF67488, (ulong) 0x3F6EF00A8329163C,
                    0x8E5A7E42FDEB6591, (ulong) 0x5CAAEE4C7981DDB5,
                    (ulong) 0x19F234785AF1E80D, (ulong) 0x255DDDE3ED98BD70,
                    (ulong) 0x50898A32A99CCCAC, (ulong) 0x28CA4519DA4E6656,
                    0xAE59880F4CB31D22, (ulong) 0x0D9798FA37D6DB26,
                    (ulong) 0x32F968F0B4FFCD1A, 0xA00F09644F258545,
                    0xFA3AD5175E24DE72, 0xF46C547C5DB24615,
                    (ulong) 0x713E80FBFF0F7E20, (ulong) 0x7843CF2B73D2AAFA,
                    0xBD17EA36AEDF62B4, 0xFD111BACD16F92CF,
                    (ulong) 0x4ABAA7DBC72D67E0, 0xB3416B5DAD49FAD3,
                    0xBCA316B24914A88B, (ulong) 0x15D150068AECF914,
                    0xE27C1DEBE31EFC40, (ulong) 0x4FE48C759BEDA223,
                    (ulong) 0x7EDCFD141B522C78, (ulong) 0x4E5070F17C26681C,
                    0xE696CAC15815F3BC, (ulong) 0x35D2A64B3BB481A7,
                    0x800CFF29FE7DFDF6, (ulong) 0x1ED9FAC3D5BAA4B0,
                    (ulong) 0x6C2663A91EF599D1, (ulong) 0x03C1199134404341,
                    0xF7AD4DED69F20554, 0xCD9D9649B61BD6AB,
                    0xC8C3BDE7EADB1368, 0xD131899FB02AFB65,
                    (ulong) 0x1D18E352E1FAE7F1, 0xDA39235AEF7CA6C1,
                    0xA1BBF5E0A8EE4F7A, 0x91377805CF9A0B1E,
                    (ulong) 0x3138716180BF8E5B, 0xD9F83ACBDB3CE580,
                    (ulong) 0x0275E515D38B897E, (ulong) 0x472D3F21F0FBBCC6,
                    (ulong) 0x2D946EB7868EA395, 0xBA3C248D21942E09,
                    0xE7223645BFDE3983, 0xFF64FEB902E41BB1,
                    0xC97741630D10D957, 0xC3CB1722B58D4ECC,
                    0xA27AEC719CAE0C3B, 0x99FECB51A48C15FB,
                    (ulong) 0x1465AC826D27332B, 0xE1BD047AD75EBF01,
                    (ulong) 0x79F733AF941960C5, (ulong) 0x672EC96C41A3C475,
                    0xC27FEBA6524684F3, (ulong) 0x64EFD0FD75E38734,
                    0xED9E60040743AE18, 0xFB8E2993B9EF144D,
                    (ulong) 0x38453EB10C625A81, (ulong) 0x6978480742355C12,
                    (ulong) 0x48CF42CE14A6EE9E, (ulong) 0x1CAC1FD606312DCE,
                    (ulong) 0x7B82D6BA4792E9BB, 0x9D141C7B1F871A07,
                    (ulong) 0x5616B80DC11C4A2E, 0xB849C198F21FA777,
                    (ulong) 0x7CA91801C8D9A506, 0xB1348E487EC273AD,
                    (ulong) 0x41B20D1E987B3A44, (ulong) 0x7460AB55A3CFBBE3,
                    0x84E628034576F20A, (ulong) 0x1B87D16D897A6173,
                    (ulong) 0x0FE27DEFE45D5258, 0x83CDE6B8CA3DBEB7,
                    (ulong) 0x0C23647ED01D1119, (ulong) 0x7A362A3EA0592384,
                    0xB61F40F3F1893F10, (ulong) 0x75D457D1440471DC,
                    (ulong) 0x4558DA34237035B8, 0xDCA6116587FC2043,
                    0x8D9B67D3C9AB26D0, (ulong) 0x2B0B5C88EE0E2517,
                    (ulong) 0x6FE77A382AB5DA90, (ulong) 0x269CC472D9D8FE31,
                    (ulong) 0x63C41E46FAA8CB89, 0xB7ABBC771642F52F,
                    (ulong) 0x7D1DE4852F126F39, 0xA8C6BA3024339BA0,
                    (ulong) 0x600507D7CEE888C8, 0x8FEE82C61A20AFAE,
                    (ulong) 0x57A2448926D78011, 0xFCA5E72836A458F0,
                    (ulong) 0x072BCEBB8F4B4CBD, (ulong) 0x497BBE4AF36D24A1,
                    (ulong) 0x3CAFE99BB769557D, (ulong) 0x12FA9EBD05A7B5A9,
                    0xE8C04BAA5B836BDB, (ulong) 0x4273148FAC3B7905,
                    0x908384812851C121, 0xE557D3506C55B0FD,
                    (ulong) 0x72FF996ACB4F3D61, (ulong) 0x3EDA0C8E64E2DC03,
                    0xF0868356E6B949E9, (ulong) 0x04EAD72ABB0B0FFC,
                    (ulong) 0x17A4B5135967706A, 0xE3C8E16F04D5367F,
                    0xF84F30028DAF570C, (ulong) 0x1846C8FCBD3A2232,
                    (ulong) 0x5B8120F7F6CA9108, 0xD46FA231ECEA3EA6,
                    (ulong) 0x334D947453340725, (ulong) 0x58403966C28AD249,
                    0xBED6F3A79A9F21F5, (ulong) 0x68CCB483A5FE962D,
                    0xD085751B57E1315A, 0xFED0023DE52FD18E,
                    (ulong) 0x4B0E5B5F20E6ADDF, (ulong) 0x1A332DE96EB1AB4C,
                    0xA3CE10F57B65C604, (ulong) 0x108F7BA8D62C3CD7,
                    0xAB07A3A11073D8E1, (ulong) 0x6B0DAD1291BED56C,
                    0xF2F366433532C097, (ulong) 0x2E557726B2CEE0D4,
                    (ulong) 0x0000000000000000, 0xCB02A476DE9B5029,
                    0xE4E32FD48B9E7AC2, (ulong) 0x734B65EE2C84F75E,
                    (ulong) 0x6E5386BCCD7E10AF, (ulong) 0x01B4FC84E7CBCA3F,
                    0xCFE8735C65905FD5, (ulong) 0x3613BFDA0FF4C2E6,
                    (ulong) 0x113B872C31E7F6E8, (ulong) 0x2FE18BA255052AEB,
                    0xE974B72EBC48A1E4, (ulong) 0x0ABC5641B89D979B,
                    0xB46AA5E62202B66E, (ulong) 0x44EC26B0C4BBFF87,
                    0xA6903B5B27A503C7, (ulong) 0x7F680190FC99E647,
                    0x97A84A3AA71A8D9C, 0xDD12EDE16037EA7C,
                    0xC554251DDD0DC84E, 0x88C54C7D956BE313,
                    (ulong) 0x4D91696048662B5D, 0xB08072CC9909B992,
                    0xB5DE5962C5C97C51, 0x81B803AD19B637C9,
                    0xB2F597D94A8230EC, (ulong) 0x0B08AAC55F565DA4,
                    0xF1327FD2017283D6, 0xAD98919E78F35E63,
                    (ulong) 0x6AB9519676751F53, (ulong) 0x24E921670A53774F,
                    0xB9FD3D1C15D46D48, 0x92F66194FBDA485F,
                    (ulong) 0x5A35DC7311015B37, 0xDED3F4705477A93D,
                    0xC00A0EB381CD0D8D, 0xBB88D809C65FE436,
                    (ulong) 0x16104997BEACBA55, (ulong) 0x21B70AC95693B28C,
                    (ulong) 0x59F4C5E225411876, 0xD5DB5EB50B21F499,
                    (ulong) 0x55D7A19CF55C096F, 0xA97246B4C3F8519F,
                    0x8552D487A2BD3835, (ulong) 0x54635D181297C350,
                    (ulong) 0x23C2EFDC85183BF2, 0x9F61F96ECC0C9379,
                    (ulong) 0x534893A39DDC8FED, (ulong) 0x5EDF0B59AA0A54CB,
                    0xAC2C6D1A9F38945C, 0xD7AEBBA0D8AA7DE7,
                    (ulong) 0x2ABFA00C09C5EF28, 0xD84CC64F3CF72FBF,
                    (ulong) 0x2003F64DB15878B3, 0xA724C7DFC06EC9F8,
                    (ulong) 0x069F323F68808682, 0xCC296ACD51D01C94,
                    (ulong) 0x055E2BAE5CC0C5C3, (ulong) 0x6270E2C21D6301B6,
                    (ulong) 0x3B842720382219C0, 0xD2F0900E846AB824,
                    (ulong) 0x52FC6F277A1745D2, 0xC6953C8CE94D8B0F,
                    0xE009F8FE3095753E, (ulong) 0x655B2C7992284D0B,
                    0x984A37D54347DFC4, 0xEAB5AEBF8808E2A5,
                    0x9A3FD2C090CC56BA, 0x9CA0E0FFF84CD038,
                    (ulong) 0x4C2595E4AFADE162, 0xDF6708F4B3BC6302,
                    0xBF620F237D54EBCA, 0x93429D101C118260,
                    (ulong) 0x097D4FD08CDDD4DA, 0x8C2F9B572E60ECEF,
                    (ulong) 0x708A7C7F18C4B41F, (ulong) 0x3A30DBA4DFE9D3FF,
                    (ulong) 0x4006F19A7FB0F07B, (ulong) 0x5F6BF7DD4DC19EF4,
                    (ulong) 0x1F6D064732716E8F, 0xF9FBCC866A649D33,
                    (ulong) 0x308C8DE567744464, 0x8971B0F972A0292C,
                    0xD61A47243F61B7D8, 0xEFEB8511D4C82766,
                    0x961CB6BE40D147A3, 0xAAB35F25F7B812DE,
                    (ulong) 0x76154E407044329D, (ulong) 0x513D76B64E570693,
                    0xF3479AC7D2F90AA8, 0x9B8B2E4477079C85,
                    (ulong) 0x297EB99D3D85AC69
                },
                new[]
                {
                    (ulong) 0x7E37E62DFC7D40C3,
                    (ulong) 0x776F25A4EE939E5B, 0xE045C850DD8FB5AD,
                    0x86ED5BA711FF1952, 0xE91D0BD9CF616B35,
                    (ulong) 0x37E0AB256E408FFB, 0x9607F6C031025A7A,
                    (ulong) 0x0B02F5E116D23C9D, 0xF3D8486BFB50650C,
                    (ulong) 0x621CFF27C40875F5, (ulong) 0x7D40CB71FA5FD34A,
                    (ulong) 0x6DAA6616DAA29062, 0x9F5F354923EC84E2,
                    0xEC847C3DC507C3B3, (ulong) 0x025A3668043CE205,
                    0xA8BF9E6C4DAC0B19, 0xFA808BE2E9BEBB94,
                    0xB5B99C5277C74FA3, (ulong) 0x78D9BC95F0397BCC,
                    0xE332E50CDBAD2624, 0xC74FCE129332797E,
                    (ulong) 0x1729ECEB2EA709AB, 0xC2D6B9F69954D1F8,
                    (ulong) 0x5D898CBFBAB8551A, 0x859A76FB17DD8ADB,
                    (ulong) 0x1BE85886362F7FB5, 0xF6413F8FF136CD8A,
                    0xD3110FA5BBB7E35C, (ulong) 0x0A2FEED514CC4D11,
                    0xE83010EDCD7F1AB9, 0xA1E75DE55F42D581,
                    0xEEDE4A55C13B21B6, 0xF2F5535FF94E1480,
                    (ulong) 0x0CC1B46D1888761E, 0xBCE15FDB6529913B,
                    (ulong) 0x2D25E8975A7181C2, (ulong) 0x71817F1CE2D7A554,
                    (ulong) 0x2E52C5CB5C53124B, 0xF9F7A6BEEF9C281D,
                    0x9E722E7D21F2F56E, 0xCE170D9B81DCA7E6,
                    (ulong) 0x0E9B82051CB4941B, (ulong) 0x1E712F623C49D733,
                    (ulong) 0x21E45CFA42F9F7DC, 0xCB8E7A7F8BBA0F60,
                    0x8E98831A010FB646, (ulong) 0x474CCF0D8E895B23,
                    0xA99285584FB27A95, 0x8CC2B57205335443,
                    (ulong) 0x42D5B8E984EFF3A5, (ulong) 0x012D1B34021E718C,
                    (ulong) 0x57A6626AAE74180B, 0xFF19FC06E3D81312,
                    (ulong) 0x35BA9D4D6A7C6DFE, 0xC9D44C178F86ED65,
                    (ulong) 0x506523E6A02E5288, (ulong) 0x03772D5C06229389,
                    0x8B01F4FE0B691EC0, 0xF8DABD8AED825991,
                    (ulong) 0x4C4E3AEC985B67BE, 0xB10DF0827FBF96A9,
                    (ulong) 0x6A69279AD4F8DAE1, 0xE78689DCD3D5FF2E,
                    0x812E1A2B1FA553D1, 0xFBAD90D6EBA0CA18,
                    (ulong) 0x1AC543B234310E39, (ulong) 0x1604F7DF2CB97827,
                    0xA6241C6951189F02, (ulong) 0x753513CCEAAF7C5E,
                    (ulong) 0x64F2A59FC84C4EFA, (ulong) 0x247D2B1E489F5F5A,
                    0xDB64D718AB474C48, (ulong) 0x79F4A7A1F2270A40,
                    (ulong) 0x1573DA832A9BEBAE, (ulong) 0x3497867968621C72,
                    (ulong) 0x514838D2A2302304, 0xF0AF6537FD72F685,
                    (ulong) 0x1D06023E3A6B44BA, (ulong) 0x678588C3CE6EDD73,
                    (ulong) 0x66A893F7CC70ACFF, 0xD4D24E29B5EDA9DF,
                    (ulong) 0x3856321470EA6A6C, (ulong) 0x07C3418C0E5A4A83,
                    (ulong) 0x2BCBB22F5635BACD, (ulong) 0x04B46CD00878D90A,
                    (ulong) 0x06EE5AB80C443B0F, (ulong) 0x3B211F4876C8F9E5,
                    (ulong) 0x0958C38912EEDE98, 0xD14B39CDBF8B0159,
                    (ulong) 0x397B292072F41BE0, 0x87C0409313E168DE,
                    0xAD26E98847CAA39F, (ulong) 0x4E140C849C6785BB,
                    0xD5FF551DB7F3D853, 0xA0CA46D15D5CA40D,
                    0xCD6020C787FE346F, 0x84B76DCF15C3FB57,
                    0xDEFDA0FCA121E4CE, (ulong) 0x4B8D7B6096012D3D,
                    0x9AC642AD298A2C64, (ulong) 0x0875D8BD10F0AF14,
                    0xB357C6EA7B8374AC, (ulong) 0x4D6321D89A451632,
                    0xEDA96709C719B23F, 0xF76C24BBF328BC06,
                    0xC662D526912C08F2, (ulong) 0x3CE25EC47892B366,
                    0xB978283F6F4F39BD, 0xC08C8F9E9D6833FD,
                    (ulong) 0x4F3917B09E79F437, (ulong) 0x593DE06FB2C08C10,
                    0xD6887841B1D14BDA, (ulong) 0x19B26EEE32139DB0,
                    0xB494876675D93E2F, 0x825937771987C058,
                    0x90E9AC783D466175, 0xF1827E03FF6C8709,
                    0x945DC0A8353EB87F, (ulong) 0x4516F9658AB5B926,
                    (ulong) 0x3F9573987EB020EF, 0xB855330B6D514831,
                    (ulong) 0x2AE6A91B542BCB41, (ulong) 0x6331E413C6160479,
                    (ulong) 0x408F8E8180D311A0, 0xEFF35161C325503A,
                    0xD06622F9BD9570D5, 0x8876D9A20D4B8D49,
                    0xA5533135573A0C8B, 0xE168D364DF91C421,
                    0xF41B09E7F50A2F8F, (ulong) 0x12B09B0F24C1A12D,
                    0xDA49CC2CA9593DC4, (ulong) 0x1F5C34563E57A6BF,
                    (ulong) 0x54D14F36A8568B82, 0xAF7CDFE043F6419A,
                    0xEA6A2685C943F8BC, 0xE5DCBFB4D7E91D2B,
                    0xB27ADDDE799D0520, (ulong) 0x6B443CAED6E6AB6D,
                    (ulong) 0x7BAE91C9F61BE845, (ulong) 0x3EB868AC7CAE5163,
                    (ulong) 0x11C7B65322E332A4, 0xD23C1491B9A992D0,
                    0x8FB5982E0311C7CA, (ulong) 0x70AC6428E0C9D4D8,
                    0x895BC2960F55FCC5, (ulong) 0x76423E90EC8DEFD7,
                    (ulong) 0x6FF0507EDE9E7267, (ulong) 0x3DCF45F07A8CC2EA,
                    (ulong) 0x4AA06054941F5CB1, (ulong) 0x5810FB5BB0DEFD9C,
                    (ulong) 0x5EFEA1E3BC9AC693, (ulong) 0x6EDD4B4ADC8003EB,
                    (ulong) 0x741808F8E8B10DD2, (ulong) 0x145EC1B728859A22,
                    (ulong) 0x28BC9F7350172944, (ulong) 0x270A06424EBDCCD3,
                    0x972AEDF4331C2BF6, (ulong) 0x059977E40A66A886,
                    (ulong) 0x2550302A4A812ED6, 0xDD8A8DA0A7037747,
                    0xC515F87A970E9B7B, (ulong) 0x3023EAA9601AC578,
                    0xB7E3AA3A73FBADA6, (ulong) 0x0FB699311EAAE597,
                    (ulong) 0x0000000000000000, (ulong) 0x310EF19D6204B4F4,
                    (ulong) 0x229371A644DB6455, (ulong) 0x0DECAF591A960792,
                    (ulong) 0x5CA4978BB8A62496, (ulong) 0x1C2B190A38753536,
                    (ulong) 0x41A295B582CD602C, (ulong) 0x3279DCC16426277D,
                    0xC1A194AA9F764271, (ulong) 0x139D803B26DFD0A1,
                    0xAE51C4D441E83016, 0xD813FA44AD65DFC1,
                    0xAC0BF2BC45D4D213, (ulong) 0x23BE6A9246C515D9,
                    (ulong) 0x49D74D08923DCF38, 0x9D05032127D066E7,
                    (ulong) 0x2F7FDEFF5E4D63C7, 0xA47E2A0155247D07,
                    0x99B16FF12FA8BFED, (ulong) 0x4661D4398C972AAF,
                    0xDFD0BBC8A33F9542, 0xDCA79694A51D06CB,
                    0xB020EBB67DA1E725, 0xBA0F0563696DAA34,
                    0xE4F1A480D5F76CA7, 0xC438E34E9510EAF7,
                    0x939E81243B64F2FC, 0x8DEFAE46072D25CF,
                    (ulong) 0x2C08F3A3586FF04E, 0xD7A56375B3CF3A56,
                    (ulong) 0x20C947CE40E78650, (ulong) 0x43F8A3DD86F18229,
                    (ulong) 0x568B795EAC6A6987, 0x8003011F1DBB225D,
                    0xF53612D3F7145E03, (ulong) 0x189F75DA300DEC3C,
                    0x9570DB9C3720C9F3, 0xBB221E576B73DBB8,
                    (ulong) 0x72F65240E4F536DD, (ulong) 0x443BE25188ABC8AA,
                    0xE21FFE38D9B357A8, 0xFD43CA6EE7E4F117,
                    0xCAA3614B89A47EEC, 0xFE34E732E1C6629E,
                    0x83742C431B99B1D4, 0xCF3A16AF83C2D66A,
                    0xAAE5A8044990E91C, (ulong) 0x26271D764CA3BD5F,
                    0x91C4B74C3F5810F9, (ulong) 0x7C6DD045F841A2C6,
                    (ulong) 0x7F1AFD19FE63314F, 0xC8F957238D989CE9,
                    0xA709075D5306EE8E, (ulong) 0x55FC5402AA48FA0E,
                    (ulong) 0x48FA563C9023BEB4, (ulong) 0x65DFBEABCA523F76,
                    (ulong) 0x6C877D22D8BCE1EE, 0xCC4D3BF385E045E3,
                    0xBEBB69B36115733E, (ulong) 0x10EAAD6720FD4328,
                    0xB6CEB10E71E5DC2A, 0xBDCC44EF6737E0B7,
                    (ulong) 0x523F158EA412B08D, 0x989C74C52DB6CE61,
                    0x9BEB59992B945DE8, 0x8A2CEFCA09776F4C,
                    0xA3BD6B8D5B7E3784, 0xEB473DB1CB5D8930,
                    0xC3FBA2C29B4AA074, 0x9C28181525CE176B,
                    (ulong) 0x683311F2D0C438E4, (ulong) 0x5FD3BAD7BE84B71F,
                    0xFC6ED15AE5FA809B, (ulong) 0x36CDB0116C5EFE77,
                    (ulong) 0x29918447520958C8, 0xA29070B959604608,
                    (ulong) 0x53120EBAA60CC101, (ulong) 0x3A0C047C74D68869,
                    (ulong) 0x691E0AC6D2DA4968, (ulong) 0x73DB4974E6EB4751,
                    (ulong) 0x7A838AFDF40599C9, (ulong) 0x5A4ACD33B4E21F99,
                    (ulong) 0x6046C94FC03497F0, 0xE6AB92E8D1CB8EA2,
                    (ulong) 0x3354C7F5663856F1, 0xD93EE170AF7BAE4D,
                    (ulong) 0x616BD27BC22AE67C, 0x92B39A10397A8370,
                    0xABC8B3304B8E9890, 0xBF967287630B02B2,
                    (ulong) 0x5B67D607B6FC6E15
                },
                new[]
                {
                    0xD031C397CE553FE6,
                    (ulong) 0x16BA5B01B006B525, 0xA89BADE6296E70C8,
                    (ulong) 0x6A1F525D77D3435B, (ulong) 0x6E103570573DFA0B,
                    (ulong) 0x660EFB2A17FC95AB, (ulong) 0x76327A9E97634BF6,
                    (ulong) 0x4BAD9D6462458BF5, 0xF1830CAEDBC3F748,
                    0xC5C8F542669131FF, 0x95044A1CDC48B0CB,
                    0x892962DF3CF8B866, 0xB0B9E208E930C135,
                    0xA14FB3F0611A767C, 0x8D2605F21C160136,
                    0xD6B71922FECC549E, (ulong) 0x37089438A5907D8B,
                    (ulong) 0x0B5DA38E5803D49C, (ulong) 0x5A5BCC9CEA6F3CBC,
                    0xEDAE246D3B73FFE5, 0xD2B87E0FDE22EDCE,
                    (ulong) 0x5E54ABB1CA8185EC, (ulong) 0x1DE7F88FE80561B9,
                    0xAD5E1A870135A08C, (ulong) 0x2F2ADBD665CECC76,
                    (ulong) 0x5780B5A782F58358, (ulong) 0x3EDC8A2EEDE47B3F,
                    0xC9D95C3506BEE70F, 0x83BE111D6C4E05EE,
                    0xA603B90959367410, (ulong) 0x103C81B4809FDE5D,
                    (ulong) 0x2C69B6027D0C774A, (ulong) 0x399080D7D5C87953,
                    (ulong) 0x09D41E16487406B4, 0xCDD63B1826505E5F,
                    0xF99DC2F49B0298E8, 0x9CD0540A943CB67F,
                    0xBCA84B7F891F17C5, (ulong) 0x723D1DB3B78DF2A6,
                    (ulong) 0x78AA6E71E73B4F2E, (ulong) 0x1433E699A071670D,
                    0x84F21BE454620782, 0x98DF3327B4D20F2F,
                    0xF049DCE2D3769E5C, 0xDB6C60199656EB7A,
                    (ulong) 0x648746B2078B4783, (ulong) 0x32CD23598DCBADCF,
                    (ulong) 0x1EA4955BF0C7DA85, 0xE9A143401B9D46B5,
                    0xFD92A5D9BBEC21B8, 0xC8138C790E0B8E1B,
                    (ulong) 0x2EE00B9A6D7BA562, 0xF85712B893B7F1FC,
                    0xEB28FED80BEA949D, (ulong) 0x564A65EB8A40EA4C,
                    (ulong) 0x6C9988E8474A2823, (ulong) 0x4535898B121D8F2D,
                    0xABD8C03231ACCBF4, 0xBA2E91CAB9867CBD,
                    (ulong) 0x7960BE3DEF8E263A, (ulong) 0x0C11A977602FD6F0,
                    0xCB50E1AD16C93527, 0xEAE22E94035FFD89,
                    (ulong) 0x2866D12F5DE2CE1A, 0xFF1B1841AB9BF390,
                    0x9F9339DE8CFE0D43, 0x964727C8C48A0BF7,
                    (ulong) 0x524502C6AAAE531C, 0x9B9C5EF3AC10B413,
                    (ulong) 0x4FA2FA4942AB32A5, (ulong) 0x3F165A62E551122B,
                    0xC74148DA76E6E3D7, 0x924840E5E464B2A7,
                    0xD372AE43D69784DA, (ulong) 0x233B72A105E11A86,
                    0xA48A04914941A638, 0xB4B68525C9DE7865,
                    0xDDEABAACA6CF8002, (ulong) 0x0A9773C250B6BD88,
                    0xC284FFBB5EBD3393, 0x8BA0DF472C8F6A4E,
                    (ulong) 0x2AEF6CB74D951C32, (ulong) 0x427983722A318D41,
                    (ulong) 0x73F7CDFFBF389BB2, (ulong) 0x074C0AF9382C026C,
                    0x8A6A0F0B243A035A, (ulong) 0x6FDAE53C5F88931F,
                    0xC68B98967E538AC3, (ulong) 0x44FF59C71AA8E639,
                    0xE2FCE0CE439E9229, 0xA20CDE2479D8CD40,
                    (ulong) 0x19E89FA2C8EBD8E9, 0xF446BBCFF398270C,
                    (ulong) 0x43B3533E2284E455, 0xD82F0DCD8E945046,
                    (ulong) 0x51066F12B26CE820, 0xE73957AF6BC5426D,
                    (ulong) 0x081ECE5A40C16FA0, (ulong) 0x3B193D4FC5BFAB7B,
                    (ulong) 0x7FE66488DF174D42, (ulong) 0x0E9814EF705804D8,
                    0x8137AC857C39D7C6, 0xB1733244E185A821,
                    (ulong) 0x695C3F896F11F867, 0xF6CF0657E3EFF524,
                    (ulong) 0x1AABF276D02963D5, (ulong) 0x2DA3664E75B91E5E,
                    (ulong) 0x0289BD981077D228, 0x90C1FD7DF413608F,
                    (ulong) 0x3C5537B6FD93A917, 0xAA12107E3919A2E0,
                    (ulong) 0x0686DAB530996B78, 0xDAA6B0559EE3826E,
                    0xC34E2FF756085A87, (ulong) 0x6D5358A44FFF4137,
                    0xFC587595B35948AC, (ulong) 0x7CA5095CC7D5F67E,
                    0xFB147F6C8B754AC0, 0xBFEB26AB91DDACF9,
                    (ulong) 0x6896EFC567A49173, 0xCA9A31E11E7C5C33,
                    0xBBE44186B13315A9, (ulong) 0x0DDB793B689ABFE4,
                    (ulong) 0x70B4A02BA7FA208E, 0xE47A3A7B7307F951,
                    0x8CECD5BE14A36822, 0xEEED49B923B144D9,
                    (ulong) 0x17708B4DB8B3DC31, (ulong) 0x6088219F2765FED3,
                    0xB3FA8FDCF1F27A09, 0x910B2D31FCA6099B,
                    (ulong) 0x0F52C4A378ED6DCC, (ulong) 0x50CCBF5EBAD98134,
                    (ulong) 0x6BD582117F662A4F, 0x94CE9A50D4FDD9DF,
                    (ulong) 0x2B25BCFB45207526, (ulong) 0x67C42B661F49FCBF,
                    (ulong) 0x492420FC723259DD, (ulong) 0x03436DD418C2BB3C,
                    (ulong) 0x1F6E4517F872B391, 0xA08563BC69AF1F68,
                    0xD43EA4BAEEBB86B6, (ulong) 0x01CAD04C08B56914,
                    0xAC94CACB0980C998, (ulong) 0x54C3D8739A373864,
                    (ulong) 0x26FEC5C02DBACAC2, 0xDEA9D778BE0D3B3E,
                    (ulong) 0x040F672D20EEB950, 0xE5B0EA377BB29045,
                    0xF30AB136CBB42560, (ulong) 0x62019C0737122CFB,
                    0xE86B930C13282FA1, 0xCC1CEB542EE5374B,
                    (ulong) 0x538FD28AA21B3A08, (ulong) 0x1B61223AD89C0AC1,
                    (ulong) 0x36C24474AD25149F, (ulong) 0x7A23D3E9F74C9D06,
                    0xBE21F6E79968C5ED, 0xCF5F868036278C77,
                    0xF705D61BEB5A9C30, (ulong) 0x4D2B47D152DCE08D,
                    (ulong) 0x5F9E7BFDC234ECF8, (ulong) 0x247778583DCD18EA,
                    0x867BA67C4415D5AA, (ulong) 0x4CE1979D5A698999,
                    (ulong) 0x0000000000000000, 0xEC64F42133C696F1,
                    0xB57C5569C16B1171, 0xC1C7926F467F88AF,
                    (ulong) 0x654D96FE0F3E2E97, (ulong) 0x15F936D5A8C40E19,
                    0xB8A72C52A9F1AE95, 0xA9517DAA21DB19DC,
                    (ulong) 0x58D27104FA18EE94, (ulong) 0x5918A148F2AD8780,
                    (ulong) 0x5CDD1629DAF657C4, 0x8274C15164FB6CFA,
                    0xD1FB13DBC6E056F2, (ulong) 0x7D6FD910CF609F6A,
                    0xB63F38BDD9A9AA4D, (ulong) 0x3D9FE7FAF526C003,
                    (ulong) 0x74BBC706871499DE, 0xDF630734B6B8522A,
                    (ulong) 0x3AD3ED03CD0AC26F, 0xFADEAF2083C023D4,
                    0xC00D42234ECAE1BB, 0x8538CBA85CD76E96,
                    0xC402250E6E2458EB, (ulong) 0x47BC3413026A5D05,
                    0xAFD7A71F114272A4, 0x978DF784CC3F62E3,
                    0xB96DFC1EA144C781, (ulong) 0x21B2CF391596C8AE,
                    (ulong) 0x318E4E8D950916F3, 0xCE9556CC3E92E563,
                    (ulong) 0x385A509BDD7D1047, (ulong) 0x358129A0B5E7AFA3,
                    0xE6F387E363702B79, 0xE0755D5653E94001,
                    (ulong) 0x7BE903A5FFF9F412, (ulong) 0x12B53C2C90E80C75,
                    (ulong) 0x3307F315857EC4DB, 0x8FAFB86A0C61D31E,
                    0xD9E5DD8186213952, (ulong) 0x77F8AAD29FD622E2,
                    (ulong) 0x25BDA814357871FE, (ulong) 0x7571174A8FA1F0CA,
                    (ulong) 0x137FEC60985D6561, (ulong) 0x30449EC19DBC7FE7,
                    0xA540D4DD41F4CF2C, 0xDC206AE0AE7AE916,
                    (ulong) 0x5B911CD0E2DA55A8, 0xB2305F90F947131D,
                    (ulong) 0x344BF9ECBD52C6B7, (ulong) 0x5D17C665D2433ED0,
                    (ulong) 0x18224FEEC05EB1FD, 0x9E59E992844B6457,
                    0x9A568EBFA4A5DD07, 0xA3C60E68716DA454,
                    (ulong) 0x7E2CB4C4D7A22456, 0x87B176304CA0BCBE,
                    (ulong) 0x413AEEA632F3367D, 0x9915E36BBC67663B,
                    (ulong) 0x40F03EEA3A465F69, (ulong) 0x1C2D28C3E0B008AD,
                    (ulong) 0x4E682A054A1E5BB1, (ulong) 0x05C5B761285BD044,
                    0xE1BF8D1A5B5C2915, 0xF2C0617AC3014C74,
                    0xB7F5E8F1D11CC359, (ulong) 0x63CB4C4B3FA745EF,
                    0x9D1A84469C89DF6B, 0xE33630824B2BFB3D,
                    0xD5F474F6E60EEFA2, 0xF58C6B83FB2D4E18,
                    (ulong) 0x4676E45F0ADF3411, (ulong) 0x20781F751D23A1BA,
                    0xBD629B3381AA7ED1, 0xAE1D775319F71BB0,
                    0xFED1C80DA32E9A84, (ulong) 0x5509083F92825170,
                    (ulong) 0x29AC01635557A70E, 0xA7C9694551831D04,
                    0x8E65682604D4BA0A, (ulong) 0x11F651F8882AB749,
                    0xD77DC96EF6793D8A, 0xEF2799F52B042DCD,
                    (ulong) 0x48EEF0B07A8730C9, (ulong) 0x22F1A2ED0D547392,
                    (ulong) 0x6142F1D32FD097C7, (ulong) 0x4A674D286AF0E2E1,
                    0x80FD7CC9748CBED2, (ulong) 0x717E7067AF4F499A,
                    0x938290A9ECD1DBB3, 0x88E3B293344DD172,
                    (ulong) 0x2734158C250FA3D6
                }
            };
        }

        protected unsafe GOST3411_2012(int hashSize, byte[] iv)
            : base(hashSize, 64)
        {
            IV = new byte[64];
            N = new byte[64];
            Sigma = new byte[64];
            Ki = new byte[64];
            M = new byte[64];
            H = new byte[64];

            // Temporary buffers
            Tmp = new byte[64];
            Block = new byte[64];

            Offset = 64;

            fixed (byte* src = iv, dest = IV, dest2 = H)
            {
                PointerUtils.MemMove(dest, src, 64);
                PointerUtils.MemMove(dest2, src, 64);
            }
        }

        public override unsafe void Initialize()
        {
            Offset = 64;

            ArrayUtils.ZeroFill(N);
            ArrayUtils.ZeroFill(Sigma);

            fixed (byte* src = IV, dest = H)
            {
                PointerUtils.MemMove(dest, src, 64);
            }

            ArrayUtils.ZeroFill(Block);
        }

        public override unsafe void TransformBytes(byte[] data, int index, int length)
        {
            if (data == null) throw new ArgumentNullException(nameof(data));
            Debug.Assert(index >= 0);
            Debug.Assert(length >= 0);
            Debug.Assert(index + length <= data.Length);

            while (Offset != 64 && length > 0)
            {
                InternalUpdate(data[index]);
                index++;
                length--;
            }

            while (length >= 64)
            {
                fixed (byte* src = &data[index], dest = Tmp)
                {
                    PointerUtils.MemMove(dest, src, 64);
                }

                Reverse(Tmp, Block);
                GN(H, N, Block);
                AddMod512(N, 512);
                AddMod512(Sigma, Block);

                length -= 64;
                index += 64;
            }

            while (length > 0)
            {
                InternalUpdate(data[index]);
                index++;
                length--;
            }
        }

        protected unsafe void Finish()
        {
            var lenM = 64 - Offset;

            // At this point it is certain that lenM is smaller than 64
            var i = 0;
            while (i != 64 - lenM)
            {
                M[i] = 0;
                i++;
            }

            M[63 - lenM] = 1;

            if (Offset != 64)
                fixed (byte* src = &Block[Offset], dest = &M[64 - lenM])
                {
                    PointerUtils.MemMove(dest, src, lenM);
                }

            GN(H, N, M);
            AddMod512(N, lenM * 8);
            AddMod512(Sigma, M);
            GN(H, Zero, N);
            GN(H, Zero, Sigma);

            Reverse(H, Tmp);
        }

        private void InternalUpdate(byte input)
        {
            Offset--;
            Block[Offset] = input;

            if (Offset != 0) return;
            GN(H, N, Block);
            AddMod512(N, 512);
            AddMod512(Sigma, Block);
            Offset = 64;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private unsafe void GN(byte[] h, byte[] n, byte[] m)
        {
            fixed (byte* src = h, dest = Tmp)
            {
                PointerUtils.MemMove(dest, src, 64);
            }

            Xor512(h, n);
            F(h);

            E(h, m);
            Xor512(h, Tmp);
            Xor512(h, m);
        }

        private unsafe void E(byte[] k, byte[] m)
        {
            fixed (byte* src = k, dest = Ki)
            {
                PointerUtils.MemMove(dest, src, 64);
            }

            Xor512(k, m);
            F(k);

            for (var i = 0; i < 11; i++)
            {
                Xor512(Ki, C[i]);
                F(Ki);
                Xor512(k, Ki);
                F(k);
            }

            Xor512(Ki, C[11]);
            F(Ki);
            Xor512(k, Ki);
        }

        private static void Xor512(byte[] a, byte[] b)
        {
            var i = 0;
            for (; i < 64; i++) a[i] = (byte) (a[i] ^ b[i]);
        }

        private static void F(byte[] v)
        {
            var res = new ulong[8];

            ulong r = 0;
            r ^= T[0][v[56] & 0xFF];
            r ^= T[1][v[48] & 0xFF];
            r ^= T[2][v[40] & 0xFF];
            r ^= T[3][v[32] & 0xFF];
            r ^= T[4][v[24] & 0xFF];
            r ^= T[5][v[16] & 0xFF];
            r ^= T[6][v[8] & 0xFF];
            r ^= T[7][v[0] & 0xFF];
            res[0] = r;

            r = 0;
            r ^= T[0][v[57] & 0xFF];
            r ^= T[1][v[49] & 0xFF];
            r ^= T[2][v[41] & 0xFF];
            r ^= T[3][v[33] & 0xFF];
            r ^= T[4][v[25] & 0xFF];
            r ^= T[5][v[17] & 0xFF];
            r ^= T[6][v[9] & 0xFF];
            r ^= T[7][v[1] & 0xFF];
            res[1] = r;

            r = 0;
            r ^= T[0][v[58] & 0xFF];
            r ^= T[1][v[50] & 0xFF];
            r ^= T[2][v[42] & 0xFF];
            r ^= T[3][v[34] & 0xFF];
            r ^= T[4][v[26] & 0xFF];
            r ^= T[5][v[18] & 0xFF];
            r ^= T[6][v[10] & 0xFF];
            r ^= T[7][v[2] & 0xFF];
            res[2] = r;

            r = 0;
            r ^= T[0][v[59] & 0xFF];
            r ^= T[1][v[51] & 0xFF];
            r ^= T[2][v[43] & 0xFF];
            r ^= T[3][v[35] & 0xFF];
            r ^= T[4][v[27] & 0xFF];
            r ^= T[5][v[19] & 0xFF];
            r ^= T[6][v[11] & 0xFF];
            r ^= T[7][v[3] & 0xFF];
            res[3] = r;

            r = 0;
            r ^= T[0][v[60] & 0xFF];
            r ^= T[1][v[52] & 0xFF];
            r ^= T[2][v[44] & 0xFF];
            r ^= T[3][v[36] & 0xFF];
            r ^= T[4][v[28] & 0xFF];
            r ^= T[5][v[20] & 0xFF];
            r ^= T[6][v[12] & 0xFF];
            r ^= T[7][v[4] & 0xFF];
            res[4] = r;

            r = 0;
            r ^= T[0][v[61] & 0xFF];
            r ^= T[1][v[53] & 0xFF];
            r ^= T[2][v[45] & 0xFF];
            r ^= T[3][v[37] & 0xFF];
            r ^= T[4][v[29] & 0xFF];
            r ^= T[5][v[21] & 0xFF];
            r ^= T[6][v[13] & 0xFF];
            r ^= T[7][v[5] & 0xFF];
            res[5] = r;

            r = 0;
            r ^= T[0][v[62] & 0xFF];
            r ^= T[1][v[54] & 0xFF];
            r ^= T[2][v[46] & 0xFF];
            r ^= T[3][v[38] & 0xFF];
            r ^= T[4][v[30] & 0xFF];
            r ^= T[5][v[22] & 0xFF];
            r ^= T[6][v[14] & 0xFF];
            r ^= T[7][v[6] & 0xFF];
            res[6] = r;

            r = 0;
            r ^= T[0][v[63] & 0xFF];
            r ^= T[1][v[55] & 0xFF];
            r ^= T[2][v[47] & 0xFF];
            r ^= T[3][v[39] & 0xFF];
            r ^= T[4][v[31] & 0xFF];
            r ^= T[5][v[23] & 0xFF];
            r ^= T[6][v[15] & 0xFF];
            r ^= T[7][v[7] & 0xFF];
            res[7] = r;

            r = res[0];
            v[7] = (byte) (r >> 56);
            v[6] = (byte) (r >> 48);
            v[5] = (byte) (r >> 40);
            v[4] = (byte) (r >> 32);
            v[3] = (byte) (r >> 24);
            v[2] = (byte) (r >> 16);
            v[1] = (byte) (r >> 8);
            v[0] = (byte) r;

            r = res[1];
            v[15] = (byte) (r >> 56);
            v[14] = (byte) (r >> 48);
            v[13] = (byte) (r >> 40);
            v[12] = (byte) (r >> 32);
            v[11] = (byte) (r >> 24);
            v[10] = (byte) (r >> 16);
            v[9] = (byte) (r >> 8);
            v[8] = (byte) r;

            r = res[2];
            v[23] = (byte) (r >> 56);
            v[22] = (byte) (r >> 48);
            v[21] = (byte) (r >> 40);
            v[20] = (byte) (r >> 32);
            v[19] = (byte) (r >> 24);
            v[18] = (byte) (r >> 16);
            v[17] = (byte) (r >> 8);
            v[16] = (byte) r;

            r = res[3];
            v[31] = (byte) (r >> 56);
            v[30] = (byte) (r >> 48);
            v[29] = (byte) (r >> 40);
            v[28] = (byte) (r >> 32);
            v[27] = (byte) (r >> 24);
            v[26] = (byte) (r >> 16);
            v[25] = (byte) (r >> 8);
            v[24] = (byte) r;

            r = res[4];
            v[39] = (byte) (r >> 56);
            v[38] = (byte) (r >> 48);
            v[37] = (byte) (r >> 40);
            v[36] = (byte) (r >> 32);
            v[35] = (byte) (r >> 24);
            v[34] = (byte) (r >> 16);
            v[33] = (byte) (r >> 8);
            v[32] = (byte) r;

            r = res[5];
            v[47] = (byte) (r >> 56);
            v[46] = (byte) (r >> 48);
            v[45] = (byte) (r >> 40);
            v[44] = (byte) (r >> 32);
            v[43] = (byte) (r >> 24);
            v[42] = (byte) (r >> 16);
            v[41] = (byte) (r >> 8);
            v[40] = (byte) r;

            r = res[6];
            v[55] = (byte) (r >> 56);
            v[54] = (byte) (r >> 48);
            v[53] = (byte) (r >> 40);
            v[52] = (byte) (r >> 32);
            v[51] = (byte) (r >> 24);
            v[50] = (byte) (r >> 16);
            v[49] = (byte) (r >> 8);
            v[48] = (byte) r;

            r = res[7];
            v[63] = (byte) (r >> 56);
            v[62] = (byte) (r >> 48);
            v[61] = (byte) (r >> 40);
            v[60] = (byte) (r >> 32);
            v[59] = (byte) (r >> 24);
            v[58] = (byte) (r >> 16);
            v[57] = (byte) (r >> 8);
            v[56] = (byte) r;

            ArrayUtils.ZeroFill(res);
        }

        private static void AddMod512(byte[] a, int num)
        {
            var c = (a[63] & 0xFF) + (num & 0xFF);
            a[63] = (byte) c;

            c = (a[62] & 0xFF) + (Bits.Asr32(num, 8) & 0xFF) + Bits.Asr32(c, 8);
            a[62] = (byte) c;

            var i = 61;
            while (i >= 0 && c > 0)
            {
                c = (a[i] & 0xFF) + Bits.Asr32(c, 8);
                a[i] = (byte) c;
                i--;
            }
        }

        private static void AddMod512(byte[] a, byte[] b)
        {
            var c = 0;
            var i = 63;

            while (i >= 0)
            {
                c = (a[i] & 0xFF) + (b[i] & 0xFF) + Bits.Asr32(c, 8);
                a[i] = (byte) c;
                i--;
            }
        }

        private static void Reverse(byte[] src, byte[] dst)
        {
            var len = src.Length;
            for (var i = 0; i < len; i++) dst[len - 1 - i] = src[i];
        }
    }

    internal sealed class GOST3411_2012_256 : GOST3411_2012
    {
        private static readonly byte[] IV_256 =
        {
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01
        };

        internal GOST3411_2012_256()
            : base(32, IV_256)
        {
        }

        public override IHash Clone() =>
            new GOST3411_2012_256
            {
                Offset = Offset,
                IV = ArrayUtils.Clone(IV),
                N = ArrayUtils.Clone(N),
                Sigma = ArrayUtils.Clone(Sigma),
                Ki = ArrayUtils.Clone(Ki),
                M = ArrayUtils.Clone(M),
                H = ArrayUtils.Clone(H),
                Tmp = ArrayUtils.Clone(Tmp),
                Block = ArrayUtils.Clone(Block),
                BufferSize = BufferSize
            };

        public override unsafe IHashResult TransformFinal()
        {
            Finish();
            var tempRes = new byte[HashSize];

            fixed (byte* src = &Tmp[32], dest = tempRes)
            {
                PointerUtils.MemMove(dest, src, tempRes.Length);
            }

            var result = new HashResult(tempRes);

            Initialize();

            return result;
        }
    }

    internal sealed class GOST3411_2012_512 : GOST3411_2012
    {
        private static readonly byte[] IV_512 =
        {
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
        };

        internal GOST3411_2012_512()
            : base(64, IV_512)
        {
        }

        public override IHash Clone() =>
            new GOST3411_2012_512
            {
                Offset = Offset,
                IV = ArrayUtils.Clone(IV),
                N = ArrayUtils.Clone(N),
                Sigma = ArrayUtils.Clone(Sigma),
                Ki = ArrayUtils.Clone(Ki),
                M = ArrayUtils.Clone(M),
                H = ArrayUtils.Clone(H),
                Tmp = ArrayUtils.Clone(Tmp),
                Block = ArrayUtils.Clone(Block),
                BufferSize = BufferSize
            };

        public override unsafe IHashResult TransformFinal()
        {
            Finish();
            var tempRes = new byte[HashSize];

            fixed (byte* src = Tmp, dest = tempRes)
            {
                PointerUtils.MemMove(dest, src, tempRes.Length);
            }

            var result = new HashResult(tempRes);

            Initialize();

            return result;
        }
    }
}