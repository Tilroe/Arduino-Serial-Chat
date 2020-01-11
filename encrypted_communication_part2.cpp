// ==============================================
// Names : Rowan Tilroe, Filippo Ciandy
// IDs: 1629172, 1641346
// CMPUT 274, Fall 2019
// Assignment 2 (PART 2): Encrypted Communication
// ==============================================
#include <Arduino.h>
//declares global variables
const int pin13 = 13;

void setup()
{
	init();
	// Must initialize serial port communications before using Serial.
	Serial.begin(9600);
	Serial3.begin(9600);
	pinMode(pin13, INPUT);
}

// computes a times b by adding the terms ai*(2^i * b) (where ai is the ith digit in the binary expansion of a)
// and computing the modulus after each multiplication and addtion
uint32_t mulmod(uint32_t a, uint32_t b, uint32_t m)
{
	uint32_t ans = 0;
	uint32_t twoib = b % m;
	uint32_t ai = 0;
	uint32_t term = 0;

	for (uint32_t i = 0; i < 32; i++)
	{
		if (a % 2)
		{
			term = twoib;
			ans = (ans + term) % m;
		}
		a >>= 1;
		twoib = (twoib << 1) % m;
	}
	return ans;
}

// computes the value x^pow mod m ("x to the power of pow" mod m)
uint32_t powmod(uint32_t x, uint32_t pow, uint32_t m)
{
	uint32_t ans = 1;
	uint32_t pow_x = x;

	while (pow > 0)
	{
		if (pow & 1 == 1)
		{
			ans = mulmod(ans, pow_x, m);
		}

		pow_x = mulmod(pow_x, pow_x, m);

		pow >>= 1; // divides by 2
	}

	return ans;
}
/** Writes  an  uint32_t  to Serial3 , starting  from  the least -significant* 
and  finishing  with  the  most  significant  byte.*/

void uint32_to_serial3(uint32_t num)
{
	Serial3.write((char)(num >> 0));
	Serial3.write((char)(num >> 8));
	Serial3.write((char)(num >> 16));
	Serial3.write((char)(num >> 24));
}
/** Reads an  uint32_t  from  Serial3 , starting  from  the least -significant*
 and  finishing  with  the  most  significant  byte.*/

uint32_t uint32_from_serial3()
{
	uint32_t num = 0;
	num = num | ((uint32_t)Serial3.read()) << 0;
	num = num | ((uint32_t)Serial3.read()) << 8;
	num = num | ((uint32_t)Serial3.read()) << 16;
	num = num | ((uint32_t)Serial3.read()) << 24;
	return num;
}

// wait_on_serial3 function from Assignment Description
bool wait_on_serial3(uint8_t nbytes, long timeout)
{
	unsigned long deadline = millis() + timeout;
	while (Serial3.available() < nbytes && (timeout < 0 || millis() < deadline))
	{
		delay(1);
	}
	return (Serial3.available() >= nbytes);
}

// Upper square root function from Primality morning problem
unsigned int upper_sqrt(unsigned int n)
{
	unsigned int d = sqrt((double)n);

	// should iterate at most once or twice
	while (d * d <= n)
	{
		++d;
	}

	return d;
}

// Primality test from Primality morning problem
bool isPrimeFunc(uint32_t num)
{
	bool prime = true;

	// Determine if number is prime
	if (num > 2)
	{
		uint32_t max_factor = upper_sqrt(num);
		uint32_t i = 2;

		while ((prime) && (i <= max_factor))
		{
			// Check all numbers up to sqrt of num to see if they divide num
			if ((num % i) == 0)
			{
				prime = false;
			}
			i += 1;
		}
	}
	else if (num == 2)
	{
		prime = true;
	}
	else
	{
		prime = false;
	}

	// return boolean true or false if prime or not
	if (prime)
	{
		return true;
	}
	else
	{
		return false;
	}
}

// Generates a random prime between [2^k, 2^(k+1)-1)
uint32_t generatePrime(uint32_t numBits)
{
	// 1) Generate a number by using analogRead() k times
	uint32_t number;
	uint32_t temp_number;
	uint32_t randombit;
	if (numBits == 14)
	{
		number = 16348;
	}
	else
	{
		number = 32768;
	}
	for (int i = 0; i < numBits; i++)
	{
		temp_number = analogRead(A1);
		randombit = (temp_number & 1);
		number = number + (randombit << i);
		delay(5);
	}

	// 2) Test if prime. If not, increment by 1 and test again.
	bool isPrime = isPrimeFunc(number);
	while (not isPrime)
	{
		number++;
		if (number == (1ul << (numBits + 1)))
		{
			// Wrap around if number reaches 2^(k+1)
			number = 1ul << (numBits);
		}
		// Test again
		isPrime = isPrimeFunc(number);
	}
	return number;
}

// GCD Euclid fast downloaded from eclass
uint32_t gcd_euclid_fast(uint32_t a, uint32_t b)
{
	while (b > 0)
	{
		a %= b;

		// now swap them
		uint32_t tmp = a;
		a = b;
		b = tmp;
	}
	return a; // b is 0
}

// Function to generate the encryption key
uint32_t generate_e(uint32_t phin)
{
	// Generate random 15-bit prime e until gcd(e,phin) = 1
	uint32_t e = generatePrime(15);
	while (gcd_euclid_fast(e, phin) != 1)
	{
		e = generatePrime(15);
	}
	Serial.print("e (to send to other Arduino) = ");
	Serial.println(e);

	return e;
}

// Function to generate the decryption key (i.e Get d from euclid's extended algorithm
// with e and phi(n) as inputs)
int32_t generate_d(int32_t e, int32_t phin)
{
	//Initialize arrays and starting values
	uint32_t r[40];
	int32_t s[40];
	int32_t t[40];
	int32_t q;
	int32_t i = 1;
	r[0] = phin;
	r[1] = e;
	s[0] = 1;
	s[1] = 0;
	t[0] = 0;
	t[1] = 1;

	// Actual algorithm

	while (r[i] > 0)
	{
		q = uint32_t(r[i - 1]) / uint32_t(r[i]);
		r[i + 1] = (r[i - 1] - (q * r[i]));
		s[i + 1] = (s[i - 1] - (q * s[i]));
		t[i + 1] = (t[i - 1] - (q * t[i]));

		i++;
	}

	int32_t d = t[i - 1];

	// Make sure d is in the range [0,phi(n))
	while (d < 0)
	{
		d += phin;
	}
	while (d >= phin)
	{
		d -= phin;
	}

	Serial.print("d = ");
	Serial.println(d);
	return d;
}

/**
Encrypt and decrypt do the same thing, but are duplicated for clarity and
code readability in the main function
**/
uint32_t encrypt(uint32_t c, uint32_t e, uint32_t m)
{
	uint32_t x = powmod(c, e, m);
	return x;
}

uint32_t decrypt(uint32_t x, uint32_t d, uint32_t n)
{
	uint32_t y = powmod(x, d, n);
	return y;
}

// Sends connection request to the server
void sendCR(uint32_t e, uint32_t n)
{
	// Items contained in CR:
	// ASCII value for C - 1 byte
	// Client key - 4 bytes
	// Client modulus - 4 bytes
	Serial3.write(67);
	uint32_to_serial3(e);
	uint32_to_serial3(n);
	Serial3.flush();
}

// Sends acknowledment to client
void sendACK(uint32_t e, uint32_t n)
{
	// Items contained in ACK:
	// ACII value for A - 1 byte
	// Server key - 4 bytes
	// Server modulus - 4 bytes
	Serial3.write(65);
	uint32_to_serial3(e);
	uint32_to_serial3(n);
	Serial3.flush();
}

// Main function of the program
int main()
{
	setup();

	// 1) Generate keys and modulus -----------------------------------------------------
	uint32_t d, n, sent_e, e, m, cKey, cMod, sKey, sMod;

	uint32_t p = generatePrime(14);
	uint32_t q = generatePrime(15);
	n = p * q;
	uint32_t phin = (p - 1) * (q - 1);
	Serial.print("n = ");
	Serial.print(n);
	Serial.print("   phi(n) = ");
	Serial.println(phin);
	sent_e = generate_e(phin);
	d = generate_d(sent_e, phin);
	Serial.flush();

	// 2) Handshake protocol ------------------------------------------------------------
	if (digitalRead(pin13) == HIGH)
	{
		//This arduino is the server
		Serial.println("SERVER");
		bool readyToChat = false;

		while (not readyToChat)
		{
			unsigned long deadline = millis() + 1000;

			// First listen for C
			bool listeningForC = true;
			while ((millis() < deadline) && listeningForC)
			{
				uint32_t nextByte = Serial3.read();

				if (nextByte == 67)
				{
					// "C" was read
					listeningForC = false;
				}
			}

			// Then wait for cKey and cMod and then AckofAck
			bool loop = true;
			while ((millis() < deadline) && loop)
			{

				bool waitingForKeys = true;
				while ((millis() < deadline) && waitingForKeys)
				{
					// First, waiting for key and mod

					bool eightBytes = wait_on_serial3(8, deadline - millis());
					if (eightBytes)
					{
						// cKey and cMod now being read
						waitingForKeys = false;
						cKey = uint32_from_serial3();
						cMod = uint32_from_serial3();
						sendACK(sent_e, n);
					}
				}

				bool waitingForAckofAck = true;
				while ((millis() < deadline) && waitingForAckofAck)
				{
					// Second, waiting for AckofAck
					uint32_t nextByte = Serial3.read();

					if (nextByte == 65)
					{
						// AckofAck received
						waitingForAckofAck = false;
						loop = false;
						readyToChat = true;
					}
					else if (nextByte == 67)
					{
						// Another CR received, go back to waiting for keys
						waitingForKeys = true;
					}
				}
			}
		}
		// Finally, assign Keys and mods to appropriate variables
		e = cKey;
		Serial.print("e (received) = ");
		Serial.println(e);
		m = cMod;
		Serial.print("m (modulus received) = ");
		Serial.println(m);

		Serial.println("Ready to chat");
	}

	else
	{
		//This arduino is the client
		Serial.println("CLIENT");
		bool waitingForAck = true;

		while (waitingForAck)
		{
			// Repeatedly send CR until ACK is received
			sendCR(sent_e, n);
			bool nineBytes = wait_on_serial3(9, 1000);

			if (nineBytes && (Serial3.read() == 65))
			{
				// ACK received
				sKey = uint32_from_serial3();
				sMod = uint32_from_serial3();
				waitingForAck = false;

				// Send ACK of ACK
				Serial3.write(65);
				Serial3.flush();
			}
			else
			{
				// Bad ACK, discard following 8 bytes
				for (int i = 0; i < 8; i++)
				{
					uint8_t trashByte = Serial3.read();
				}
			}
		}
		// Finally, assign Keys and mods to appropriate variables
		e = sKey;
		Serial.print("e (received) = ");
		Serial.println(e);
		m = sMod;
		Serial.print("m (modulus received) = ");
		Serial.println(m);

		Serial.println("Ready to chat");
	}

	// 3) Chatting phase ----------------------------------------------------------------
	while (true)
	{
		if (Serial.available() > 0)
		{
			// Letter typed, send to other Arduino through TX3
			char letterSent = Serial.read();
			uint32_t intLetterSent = int(letterSent);
			Serial.print(letterSent);
			uint32_to_serial3(encrypt(intLetterSent, e, m)); // Sends encrypted int

			if (int(letterSent) == 13)
			{
				// Enter key pressed: Also send a newline character
				uint32_to_serial3(encrypt(10, e, m));
				Serial.print(char(10));
			}
		}
		if (Serial3.available() > 3)
		{
			// Letter from other Arduino to be read coming from RX3
			uint32_t letterRecieved = decrypt(uint32_from_serial3(), d, n); // Recieves encrypted int
			char charLetterRecieved = char(letterRecieved);
			Serial.write(charLetterRecieved);
		}
		//flushes bit out of both buffered serial data
		Serial.flush();
		Serial3.flush();
	}
	return 0;
}
