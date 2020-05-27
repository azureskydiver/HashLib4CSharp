/*
(* &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& *)
{ *                             HashLib4CSharp Library                              * }
{ *                      Copyright (c) 2020 Ugochukwu Mmaduekwe                     * }
{ *                 GitHub Profile URL <https://github.com/Xor-el>                  * }

{ *  Distributed under the MIT software license, see the accompanying LICENSE file  * }
{ *          or visit http://www.opensource.org/licenses/mit-license.php.           * }

{ *                              Acknowledgements:                                  * }
{ *                                                                                 * }
{ *   This library was sponsored by Sphere 10 Software (https://www.sphere10.com)   * }
{ *         for the purposes of supporting the XXX (https://YYY) project.           * }
{ *                                                                                 * }
(* &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& *)
*/

using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using HashLib4CSharp.Interfaces;
using HashLib4CSharp.Utils;

namespace HashLib4CSharp.Base
{
    internal abstract class MultipleTransformNonBlock : Hash, INonBlockHash
    {
        private const string UnExpectedError = "How did it get this bad?? :(";

        protected MultipleTransformNonBlock(int hashSize, int blockSize) : base(hashSize, blockSize)
        {
            Buffer = new MemoryStream();
        }

        private MemoryStream Buffer { get; }

        ~MultipleTransformNonBlock()
        {
            Buffer?.Flush();
            Buffer?.Close();
        }

        private byte[] Aggregate()
        {
            var aggregate = new byte[0];

            if (Buffer.Length <= 0) return aggregate;
            Buffer.Position = 0;
            aggregate = new byte[Buffer.Length];
            Buffer.Read(aggregate, 0, (int) Buffer.Length);

            return aggregate;
        }

        public override IHash Clone()
        {
            var constructorInfo =
                GetType().GetTypeInfo().DeclaredConstructors
                    .First(c =>
                        (c.GetParameters().Length == 0 ||
                         c.GetParameters().Length == 1 && c.GetParameters().Any(p => p.IsOptional)) &&
                        !c.IsStatic);


            dynamic hashInstance =
                constructorInfo.Invoke(BindingFlags.CreateInstance, null, constructorInfo.GetParameters().Length == 0
                    ? null
                    : Enumerable.Repeat(Type.Missing, constructorInfo.GetParameters().Length).ToArray(), null);

            if (hashInstance == null) throw new NullReferenceHashLibException(UnExpectedError);

            var buffer = Buffer.ToArray();

            hashInstance.Buffer.Write(buffer, 0, buffer.Length);

            hashInstance.Buffer.Position = Buffer.Position;

            hashInstance.BufferSize = BufferSize;
            return hashInstance;
        }

        public override void Initialize()
        {
            Buffer.Flush();
            Buffer.SetLength(0);
        }

        public override void TransformBytes(byte[] data, int index, int length)
        {
            if (data == null) throw new ArgumentNullHashLibException(nameof(data));
            if (data.Length == 0) return;
            Debug.Assert(index >= 0);
            Debug.Assert(length >= 0);
            Debug.Assert(index + length <= data.Length);
            Buffer.Write(data, index, length);
        }

        public override IHashResult TransformFinal()
        {
            var result = ComputeAggregatedBytes(Aggregate());
            Initialize();
            return result;
        }

        public override IHashResult ComputeBytes(byte[] data)
        {
            Initialize();
            return ComputeAggregatedBytes(data);
        }

        protected abstract IHashResult ComputeAggregatedBytes(byte[] data);
    }
}