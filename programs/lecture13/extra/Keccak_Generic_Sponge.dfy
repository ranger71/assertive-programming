/*
	Based on https://blog.adacore.com/avoiding-vulnerabilities-in-crypto-code-with-spark by Daniel King – Nov 04, 2022:
	this is a partial specification and re-implementation in Dafny of the SPARK/Ada Keccak generic sponge's Absorb procedure
	(https://github.com/damaki/libkeccak/blob/master/src/common/keccak-generic_sponge.adb).

	The goal here is to implement one method, Copy, and to verify correctness of another, Absorb (see TODO nodes below).
	Documentation of the proof obligations is expected here only for the Absorb method.
*/
const MAX := 0x7FFFFFFF // == (2^31)-1 == 2147483647
const State_Size_Bits := 500
const Block_Size_Bits := State_Size_Bits

const Naturals := set n: int | 0 <= n <= MAX
const Positives := set x: int | x in Naturals && 0 < x
const Rate_Bytes_Numbers := set m: int | m in Positives && m < (State_Size_Bits + 7) / 8
const Byte_Absorption_Numbers := set n: int | 0 <= n < (State_Size_Bits + 7) / 8
const Bit_Absorption_Numbers := set n: int | n in Naturals && 0 <= n < State_Size_Bits

newtype byte = x: int | -128 <= x < 128

// no need to implement the following method
// (in our context of verifying the absence of errors such as overflow in the generic implementation of "Absorb")
method XOR_bits_into_state(a: array<int>, data: seq<byte>, bit_len: nat)
	requires |data| <= a.Length && bit_len <= State_Size_Bits && (bit_len + 7) / 8 <= |data|
	modifies a
{}

// no need to implement the following method
// (in our context of verifying the absence of errors such as overflow in the generic implementation of "Absorb")
method Permute(state: array<int>)
	modifies state
	ensures multiset(state[..]) == multiset(old(state[..]))
{}

// TODO: implement this method; no need to document proof obligations
method Copy<T>(source: seq<T>, destination: array<T>, start: nat, end: nat)
	requires start < end <= destination.Length && |source| == end - start
	modifies destination
	ensures destination[..] == old(destination[..start]) + source + old(destination[end..])

predicate Precondition(state: array<int>, block: array<byte>, bits_absorbed: nat, rate: int, data: array<byte>, bit_length: nat) {
	0 < State_Size_Bits && rate <= block.Length <= |Byte_Absorption_Numbers| == state.Length &&
	bits_absorbed < State_Size_Bits && rate in Rate_Bytes_Numbers &&
	bit_length <= MAX - 7 && (bit_length + 7) / 8 <= data.Length &&
	bits_absorbed % 8 == 0 && bits_absorbed < rate * 8
}

predicate Postcondition1_No_Overflow(bits_absorbed: nat, offset: nat, remaining_bits: nat, remaining_bytes: nat, initial_data_len: nat, initial_bit_rate: int) {
	bits_absorbed in Bit_Absorption_Numbers && offset in Naturals && remaining_bits in Naturals && remaining_bytes in Naturals && initial_data_len in Naturals &&
	initial_bit_rate in Positives
}

predicate Postcondition2(bits_absorbed: nat, bit_length: nat, rate: int) {
	bits_absorbed % 8 == bit_length % 8 && bits_absorbed < rate * 8
}

// TODO: verify correctness of this method, documenting all proof obligations as we've learned;
// don't forget to remove the "{:verify false}" annotation (or turn it into "{:verify true}")
method {:verify false} Absorb(state: array<int>, block: array<byte>, bits_absorbed0: nat, rate: int, data: array<byte>, bit_length: nat)
		returns (bits_absorbed: nat, offset: nat, remaining_bits: nat, remaining_bytes: nat, initial_data_len: nat, initial_bit_rate: int)
	requires Precondition(state, block, bits_absorbed0, rate, data, bit_length)
	modifies state, block
	ensures Postcondition1_No_Overflow(bits_absorbed, offset, remaining_bits, remaining_bytes, initial_data_len, initial_bit_rate)
	ensures Postcondition2(bits_absorbed, bit_length, rate)
{
	bits_absorbed := bits_absorbed0;
	offset := 0;
	remaining_bits := bit_length;
	remaining_bytes := (bit_length + 7) / 8;
	initial_data_len := remaining_bytes;
	initial_bit_rate := rate * 8;
	if initial_data_len > 0 {
		var free_bytes_in_block: nat, free_bits_in_block: nat, block_offset: nat;
		// Calculate how many bits are free in the 'in' queue.
		free_bits_in_block := initial_bit_rate - bits_absorbed;
		free_bytes_in_block := free_bits_in_block / 8;
		if bit_length < free_bits_in_block {
			// We don't have a complete block, so just store the message with the other leftovers.
			block_offset := bits_absorbed / 8;
			Copy(data[..initial_data_len], block, block_offset, block_offset + remaining_bytes);
			bits_absorbed := bits_absorbed + bit_length;
		}
		else {
			// Append the first data to any leftovers to get a complete block.
			if free_bits_in_block > 0 {
				block_offset := bits_absorbed / 8;
				Copy(data[..free_bytes_in_block], block, block_offset, block_offset + free_bytes_in_block);
				offset := offset + free_bytes_in_block;
				remaining_bytes := remaining_bytes - free_bytes_in_block;
				remaining_bits := remaining_bits - free_bits_in_block;
			}
			XOR_bits_into_state(state, block[..rate], initial_bit_rate);
			Permute(state);
			// Process complete blocks
			while remaining_bits >= initial_bit_rate
			{
				XOR_bits_into_state(state, data[offset..offset + rate], initial_bit_rate);
				offset := offset + rate;
				remaining_bytes := remaining_bytes - rate;
				remaining_bits := remaining_bits - initial_bit_rate;
			}
			// No more complete blocks. Store the leftovers
			if remaining_bits > 0 {
				Copy(data[offset..offset + remaining_bytes], block, 0, remaining_bytes);
			}
			bits_absorbed := remaining_bits;
		}
	}
}
