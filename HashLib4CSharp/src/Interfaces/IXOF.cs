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

namespace HashLib4CSharp.Interfaces
{
    public interface IXOF : IHash
    {
        ulong XofSizeInBits { get; set; }

        void DoOutput(byte[] dest, ulong destOffset, ulong outputLength);
    }
}