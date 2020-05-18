/*
 * Commandline-Option-Fetcher for
 * Implementation of PRESENT in C
 * v2.1, 10/13/2008
 *
 * Implementation is located at http://www.lightweightcrypto.org/implementations.php,
 * under the title "Testvectors for PRESENT".
 *
 * Thomas Siebert, thomas.siebert@rub.de
 */

#include <string.h>
#include <getopt.h>

//----------------------------------
// Function prototype
//----------------------------------
// void comline_fetch_options( struct Options * , int , char ** );

//----------------------------------
// Struct declaration
//----------------------------------
struct Options {
  _Bool Error;
  _Bool Mode;
  _Bool KeySize80;
  uint8_t Verbose;
  uint64_t KeyHigh;
  uint64_t KeyLow;
  uint64_t Text;
  uint16_t Rounds;
};

#define Encrypt_Mode 1
#define Decrypt_Mode 0

//----------------------------------
// Functions
//----------------------------------
void comline_fetch_options(struct Options *sOpt, int argc, char **const argv) {
  int c;
  _Bool Opt_Decrypt = 0, Opt_Encrypt = 0, Opt_File = 0, Opt_Verbose = 0;
  char *Opt_Text = NULL, *Opt_Key = NULL, *Opt_Rounds = NULL;
  FILE *KeyFile = NULL, *TextFile = NULL;
  int keyres;

  sOpt->Error = 0;
  sOpt->Verbose = 1;

  while ((c = getopt(argc, argv, "defv:r:k:t:")) !=
         -1)  // Cycle through Options
  {
    switch (c)  // set flags
    {
      case 'd':
        if (Opt_Encrypt || Opt_Decrypt)
          sOpt->Error = 1;
        else
          Opt_Decrypt = 1;
        break;
      case 'e':
        if (Opt_Encrypt || Opt_Decrypt)
          sOpt->Error = 1;
        else
          Opt_Encrypt = 1;
        break;
      case 'f':
        if (Opt_File)
          sOpt->Error = 1;
        else
          Opt_File = 1;
        break;
      case 'v':
        if (Opt_Verbose)
          sOpt->Error = 1;
        else if (optarg != NULL) {
          if (strcmp(optarg, "0") == 0)
            sOpt->Verbose = 0;
          else if (strcmp(optarg, "1") == 0)
            sOpt->Verbose = 1;
          else if (strcmp(optarg, "2") == 0)
            sOpt->Verbose = 2;
          else
            sOpt->Error = 1;
        } else
          sOpt->Error = 1;
        Opt_Verbose = 1;
        break;
      case 'k':
        if (Opt_Key != NULL)
          sOpt->Error = 1;
        else
          Opt_Key = optarg;
        break;
      case 'r':
        if (Opt_Rounds)
          sOpt->Error = 1;
        else
          Opt_Rounds = optarg;
        break;
      case 't':
        if (Opt_Text != NULL)
          sOpt->Error = 1;
        else
          Opt_Text = optarg;
        break;
      case '?':
        sOpt->Error = 1;
        break;
    }
  }  // End Option-Cycle

  // Set Error if Parameters missing
  if (Opt_Key == NULL || Opt_Text == NULL || (!(Opt_Decrypt || Opt_Encrypt))) {
    sOpt->Error = 1;
  }

  else {
    // Handle Rounds Parameter
    if (Opt_Rounds != NULL)  // if Round Param there...
    {
      if (strlen(Opt_Rounds) < 6)  // check length
      {
        uint32_t Rounds;
        sscanf(Opt_Rounds, "%5" SCNu32 "", &Rounds);  // get round no.
        if ((Rounds > 65534) || Rounds == 0)
          sOpt->Error = 1;  // check 0<Rounds<65535
        else
          sOpt->Rounds = Rounds;  // override roundno.
      } else
        sOpt->Error = 1;
    } else
      sOpt->Rounds = 32;  //...else use standard

    // Check if decrypt or encrypt mode
    if (Opt_Encrypt)
      sOpt->Mode = Encrypt_Mode;
    else
      sOpt->Mode = Decrypt_Mode;

    // Read key and text (file mode)
    if (Opt_File) {
      KeyFile = fopen(Opt_Key, "r");
      TextFile = fopen(Opt_Text, "r");

      if (!((KeyFile == NULL) || (TextFile) == NULL)) {
        fseek(KeyFile, 0, SEEK_END);
        if ((ftell(KeyFile)) >= 32) {
          fseek(KeyFile, 0, SEEK_SET);
          if (fscanf(KeyFile, "%016" SCNx64 "", &sOpt->KeyHigh) == 0)
            sOpt->Error = 1;
          if (fscanf(KeyFile, "%016" SCNx64 "", &sOpt->KeyLow) == 0)
            sOpt->Error = 1;
          sOpt->KeySize80 = 0;
        } else if ((ftell(KeyFile)) >= 20) {
          fseek(KeyFile, 0, SEEK_SET);
          if (fscanf(KeyFile, "%016" SCNx64 "", &sOpt->KeyHigh) == 0)
            sOpt->Error = 1;
          if (fscanf(KeyFile, "%04" SCNx16 "", &sOpt->KeyLow) == 0)
            sOpt->Error = 1;
          sOpt->KeySize80 = 1;
        } else
          sOpt->Error = 1;
        if (fscanf(TextFile, "%016" SCNx64 "", &sOpt->Text) == EOF)
          sOpt->Error = 1;
      } else
        sOpt->Error = 1;
      if (!(KeyFile == NULL))
        fclose(KeyFile);
      if (!(TextFile == NULL))
        fclose(TextFile);
    }

    // Read key and text (commandline mode)
    else {
      if (((strlen(Opt_Key) != 32) && (strlen(Opt_Key) != 20)) ||
          (strlen(Opt_Text) != 16)) {  // if wrong length...
        sOpt->Error = 1;               // set error
      }

      if (!(sOpt->Error))  // if no error...
      {
        sscanf(Opt_Key, "%016" SCNx64 "", &sOpt->KeyHigh);  // get values
        if (strlen(Opt_Key) == 20)                          // set key + size
        {
          sOpt->KeySize80 = 1;
          sscanf(Opt_Key + 16, "%016" SCNx16 "", &sOpt->KeyLow);
        } else {
          sOpt->KeySize80 = 0;
          sscanf(Opt_Key + 16, "%016" SCNx64 "", &sOpt->KeyLow);
        }
        sscanf(Opt_Text, "%016" SCNx64 "", &sOpt->Text);
      }
    }
  }
}
