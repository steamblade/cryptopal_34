from random import randint
import struct
import hashlib
from Crypto import Random
from Crypto.Cipher import AES
from binascii import unhexlify

def is_pkcs7_padded(binary_data):
    """Returns whether the data is PKCS 7 padded."""

    # Take what we expect to be the padding
    padding = binary_data[-binary_data[-1]:]

    # Check that all the bytes in the range indicated by the padding are equal to the padding value itself
    return all(padding[b] == len(padding) for b in range(0, len(padding)))

def pkcs7_pad(message, block_size):
    """Pads the given message with the PKCS 7 padding format for the given block size."""

    # If the length of the given message is already equal to the block size, there is no need to pad
    if len(message) == block_size:
        return message

    # Otherwise compute the padding byte and return the padded message
    ch = block_size - len(message) % block_size
    return message + bytes([ch] * ch)

def pkcs7_unpad(data):
    """Unpads the given data from its PKCS 7 padding and returns it."""
    if len(data) == 0:
        raise Exception("The input data must contain at least one byte")

    if not is_pkcs7_padded(data):
        return data

    padding_len = data[len(data) - 1]
    return data[:-padding_len]


def aes_ecb_encrypt(data, key):
    """Encrypts the given data with AES-ECB, using the given key.
    The data is always PKCS 7 padded before being encrypted.
    """
    cipher = AES.new(key, AES.MODE_ECB)
    return cipher.encrypt(pkcs7_pad(data, AES.block_size))

def aes_ecb_decrypt(data, key):
    """Decrypts the given AES-ECB encrypted data with the given key.
    The un-padding part has been added to support the use that I will make of this
    method on future challenges (for the sake of this challenge it's not needed).
    """
    cipher = AES.new(key, AES.MODE_ECB)
    return pkcs7_unpad(cipher.decrypt(data))

def xor_data(binary_data_1, binary_data_2):
    """Returns the xor of the two binary arrays given."""
    return bytes([b1 ^ b2 for b1, b2 in zip(binary_data_1, binary_data_2)])

def aes_cbc_encrypt(data, key, iv):
    """Encrypts the given data with AES-CBC, using the given key and iv."""
    ciphertext = b''
    prev = iv

    # Process the encryption block by block
    for i in range(0, len(data), AES.block_size):

        # Always PKCS 7 pad the current plaintext block before proceeding
        curr_plaintext_block = pkcs7_pad(data[i:i + AES.block_size], AES.block_size)
        block_cipher_input = xor_data(curr_plaintext_block, prev)
        encrypted_block = aes_ecb_encrypt(block_cipher_input, key)
        ciphertext += encrypted_block
        prev = encrypted_block

    return ciphertext

def left_rotate(value, shift):
    """Returns value left-rotated by shift bits. In other words, performs a circular shift to the left."""
    return ((value << shift) & 0xffffffff) | (value >> (32 - shift))

def sha1(message, ml=None, h0=0x67452301, h1=0xEFCDAB89, h2=0x98BADCFE, h3=0x10325476, h4=0xC3D2E1F0):
    """Returns a string containing the SHA1 hash of the input message. This is a pure python 3 SHA1
    implementation, written starting from the SHA1 pseudo-code on Wikipedia.

    The parameters ml, h0, ..., h5 are for the next challenge.
    """
    # Pre-processing:
    if ml is None:
        ml = len(message) * 8

    message += b'\x80'
    while (len(message) * 8) % 512 != 448:
        message += b'\x00'

    message += struct.pack('>Q', ml)

    # Process the message in successive 512-bit chunks:
    for i in range(0, len(message), 64):

        # Break chunk into sixteen 32-bit big-endian integers w[i]
        w = [0] * 80
        for j in range(16):
            w[j] = struct.unpack('>I', message[i + j * 4:i + j * 4 + 4])[0]

        # Extend the sixteen 32-bit integers into eighty 32-bit integers:
        for j in range(16, 80):
            w[j] = left_rotate(w[j - 3] ^ w[j - 8] ^ w[j - 14] ^ w[j - 16], 1)

        # Initialize hash value for this chunk:
        a = h0
        b = h1
        c = h2
        d = h3
        e = h4

        # Main loop
        for j in range(80):
            if j <= 19:
                f = d ^ (b & (c ^ d))
                k = 0x5A827999
            elif 20 <= j <= 39:
                f = b ^ c ^ d
                k = 0x6ED9EBA1
            elif 40 <= j <= 59:
                f = (b & c) | (d & (b | c))
                k = 0x8F1BBCDC
            else:
                f = b ^ c ^ d
                k = 0xCA62C1D6

            temp = left_rotate(a, 5) + f + e + k + w[j] & 0xffffffff
            e = d
            d = c
            c = left_rotate(b, 30)
            b = a
            a = temp

        # Add this chunk's hash to result so far:
        h0 = (h0 + a) & 0xffffffff
        h1 = (h1 + b) & 0xffffffff
        h2 = (h2 + c) & 0xffffffff
        h3 = (h3 + d) & 0xffffffff
        h4 = (h4 + e) & 0xffffffff

    # Produce the final hash value (big-endian) as a 160 bit number, hex formatted:
    return '%08x%08x%08x%08x%08x' % (h0, h1, h2, h3, h4)

def modular_pow(base, exponent, modulus):
    """Computes (base**exponent) % modulus by using the right-to-left binary method."""
    if modulus == -1:
        return 0

    result = 1
    base %= modulus

    while exponent > 0:
        if exponent % 2:
            result = (result * base) % modulus
        exponent >>= 1
        base = (base * base) % modulus

    return result

class DiffieHellman():
    """Implements the Diffie-Helman key exchange. Each class is a party, which has his secret key (usually
    referred to as lowercase a or b) shares the public key (usually referred to as uppercase A or B) and can
    compute the shared secret key between itself and another party, given their public key, assuming that
    they are agreeing on the same p and g.
    """

    DEFAULT_G = 2
    DEFAULT_P = int('ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b225'
                    '14a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f4'
                    '4c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc20'
                    '07cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed5'
                    '29077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff', 16)

    def __init__(self, g=DEFAULT_G, p=DEFAULT_P):
        self.g = g
        self.p = p
        self._secret_key = randint(0, p - 1)
        self.shared_key = None

    def get_public_key(self):
        return modular_pow(self.g, self._secret_key, self.p)

    def get_shared_secret_key(self, other_party_public_key):
        if self.shared_key is None:
            self.shared_key = modular_pow(other_party_public_key, self._secret_key, self.p)
        return self.shared_key


def aes_cbc_decrypt(data, key, iv, unpad=True):
    """Decrypts the given AES-CBC encrypted data with the given key and iv.
    Returns the unpadded decrypted message when unpad is true, or keeps the plaintext
    padded when unpad is false.
    """
    plaintext = b''
    prev = iv

    # Process the decryption block by block
    for i in range(0, len(data), AES.block_size):
        curr_ciphertext_block = data[i:i + AES.block_size]
        decrypted_block = aes_ecb_decrypt(curr_ciphertext_block, key)
        plaintext += xor_data(prev, decrypted_block)
        prev = curr_ciphertext_block

    # Return the plaintext either unpadded or left with the padding depending on the unpad flag
    return pkcs7_unpad(plaintext) if unpad else plaintext
