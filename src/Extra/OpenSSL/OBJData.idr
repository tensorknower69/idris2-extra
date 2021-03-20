module Extra.OpenSSL.OBJData

import Extra.C.Types

public export
data NID : Type where
  MkNID : CInt -> NID

-- source: https://raw.githubusercontent.com/openssl/openssl/master/crypto/objects/obj_mac.num

-- vim: :'<,'>s/^\v(.*)^I^I([0-9]+)$/public export\rNID_\1 : NID\rNID_\1 = MkNID \2\r/g
-- NOTE: substitute ^I for actual tabs

public export
NID_undef : NID
NID_undef = MkNID 0

public export
NID_rsadsi : NID
NID_rsadsi = MkNID 1

public export
NID_pkcs : NID
NID_pkcs = MkNID 2

public export
NID_md2 : NID
NID_md2 = MkNID 3

public export
NID_md5 : NID
NID_md5 = MkNID 4

public export
NID_rc4 : NID
NID_rc4 = MkNID 5

public export
NID_rsaEncryption : NID
NID_rsaEncryption = MkNID 6

public export
NID_md2WithRSAEncryption : NID
NID_md2WithRSAEncryption = MkNID 7

public export
NID_md5WithRSAEncryption : NID
NID_md5WithRSAEncryption = MkNID 8

public export
NID_pbeWithMD2AndDES_CBC : NID
NID_pbeWithMD2AndDES_CBC = MkNID 9

public export
NID_pbeWithMD5AndDES_CBC : NID
NID_pbeWithMD5AndDES_CBC = MkNID 10

public export
NID_X500 : NID
NID_X500 = MkNID 11

public export
NID_X509 : NID
NID_X509 = MkNID 12

public export
NID_commonName : NID
NID_commonName = MkNID 13

public export
NID_countryName : NID
NID_countryName = MkNID 14

public export
NID_localityName : NID
NID_localityName = MkNID 15

public export
NID_stateOrProvinceName : NID
NID_stateOrProvinceName = MkNID 16

public export
NID_organizationName : NID
NID_organizationName = MkNID 17

public export
NID_organizationalUnitName : NID
NID_organizationalUnitName = MkNID 18

public export
NID_rsa : NID
NID_rsa = MkNID 19

public export
NID_pkcs7 : NID
NID_pkcs7 = MkNID 20

public export
NID_pkcs7_data : NID
NID_pkcs7_data = MkNID 21

public export
NID_pkcs7_signed : NID
NID_pkcs7_signed = MkNID 22

public export
NID_pkcs7_enveloped : NID
NID_pkcs7_enveloped = MkNID 23

public export
NID_pkcs7_signedAndEnveloped : NID
NID_pkcs7_signedAndEnveloped = MkNID 24

public export
NID_pkcs7_digest : NID
NID_pkcs7_digest = MkNID 25

public export
NID_pkcs7_encrypted : NID
NID_pkcs7_encrypted = MkNID 26

public export
NID_pkcs3 : NID
NID_pkcs3 = MkNID 27

public export
NID_dhKeyAgreement : NID
NID_dhKeyAgreement = MkNID 28

public export
NID_des_ecb : NID
NID_des_ecb = MkNID 29

public export
NID_des_cfb64 : NID
NID_des_cfb64 = MkNID 30

public export
NID_des_cbc : NID
NID_des_cbc = MkNID 31

public export
NID_des_ede_ecb : NID
NID_des_ede_ecb = MkNID 32

public export
NID_des_ede3_ecb : NID
NID_des_ede3_ecb = MkNID 33

public export
NID_idea_cbc : NID
NID_idea_cbc = MkNID 34

public export
NID_idea_cfb64 : NID
NID_idea_cfb64 = MkNID 35

public export
NID_idea_ecb : NID
NID_idea_ecb = MkNID 36

public export
NID_rc2_cbc : NID
NID_rc2_cbc = MkNID 37

public export
NID_rc2_ecb : NID
NID_rc2_ecb = MkNID 38

public export
NID_rc2_cfb64 : NID
NID_rc2_cfb64 = MkNID 39

public export
NID_rc2_ofb64 : NID
NID_rc2_ofb64 = MkNID 40

public export
NID_sha : NID
NID_sha = MkNID 41

public export
NID_shaWithRSAEncryption : NID
NID_shaWithRSAEncryption = MkNID 42

public export
NID_des_ede_cbc : NID
NID_des_ede_cbc = MkNID 43

public export
NID_des_ede3_cbc : NID
NID_des_ede3_cbc = MkNID 44

public export
NID_des_ofb64 : NID
NID_des_ofb64 = MkNID 45

public export
NID_idea_ofb64 : NID
NID_idea_ofb64 = MkNID 46

public export
NID_pkcs9 : NID
NID_pkcs9 = MkNID 47

public export
NID_pkcs9_emailAddress : NID
NID_pkcs9_emailAddress = MkNID 48

public export
NID_pkcs9_unstructuredName : NID
NID_pkcs9_unstructuredName = MkNID 49

public export
NID_pkcs9_contentType : NID
NID_pkcs9_contentType = MkNID 50

public export
NID_pkcs9_messageDigest : NID
NID_pkcs9_messageDigest = MkNID 51

public export
NID_pkcs9_signingTime : NID
NID_pkcs9_signingTime = MkNID 52

public export
NID_pkcs9_countersignature : NID
NID_pkcs9_countersignature = MkNID 53

public export
NID_pkcs9_challengePassword : NID
NID_pkcs9_challengePassword = MkNID 54

public export
NID_pkcs9_unstructuredAddress : NID
NID_pkcs9_unstructuredAddress = MkNID 55

public export
NID_pkcs9_extCertAttributes : NID
NID_pkcs9_extCertAttributes = MkNID 56

public export
NID_netscape : NID
NID_netscape = MkNID 57

public export
NID_netscape_cert_extension : NID
NID_netscape_cert_extension = MkNID 58

public export
NID_netscape_data_type : NID
NID_netscape_data_type = MkNID 59

public export
NID_des_ede_cfb64 : NID
NID_des_ede_cfb64 = MkNID 60

public export
NID_des_ede3_cfb64 : NID
NID_des_ede3_cfb64 = MkNID 61

public export
NID_des_ede_ofb64 : NID
NID_des_ede_ofb64 = MkNID 62

public export
NID_des_ede3_ofb64 : NID
NID_des_ede3_ofb64 = MkNID 63

public export
NID_sha1 : NID
NID_sha1 = MkNID 64

public export
NID_sha1WithRSAEncryption : NID
NID_sha1WithRSAEncryption = MkNID 65

public export
NID_dsaWithSHA : NID
NID_dsaWithSHA = MkNID 66

public export
NID_dsa_2 : NID
NID_dsa_2 = MkNID 67

public export
NID_pbeWithSHA1AndRC2_CBC : NID
NID_pbeWithSHA1AndRC2_CBC = MkNID 68

public export
NID_id_pbkdf2 : NID
NID_id_pbkdf2 = MkNID 69

public export
NID_dsaWithSHA1_2 : NID
NID_dsaWithSHA1_2 = MkNID 70

public export
NID_netscape_cert_type : NID
NID_netscape_cert_type = MkNID 71

public export
NID_netscape_base_url : NID
NID_netscape_base_url = MkNID 72

public export
NID_netscape_revocation_url : NID
NID_netscape_revocation_url = MkNID 73

public export
NID_netscape_ca_revocation_url : NID
NID_netscape_ca_revocation_url = MkNID 74

public export
NID_netscape_renewal_url : NID
NID_netscape_renewal_url = MkNID 75

public export
NID_netscape_ca_policy_url : NID
NID_netscape_ca_policy_url = MkNID 76

public export
NID_netscape_ssl_server_name : NID
NID_netscape_ssl_server_name = MkNID 77

public export
NID_netscape_comment : NID
NID_netscape_comment = MkNID 78

public export
NID_netscape_cert_sequence : NID
NID_netscape_cert_sequence = MkNID 79

public export
NID_desx_cbc : NID
NID_desx_cbc = MkNID 80

public export
NID_id_ce : NID
NID_id_ce = MkNID 81

public export
NID_subject_key_identifier : NID
NID_subject_key_identifier = MkNID 82

public export
NID_key_usage : NID
NID_key_usage = MkNID 83

public export
NID_private_key_usage_period : NID
NID_private_key_usage_period = MkNID 84

public export
NID_subject_alt_name : NID
NID_subject_alt_name = MkNID 85

public export
NID_issuer_alt_name : NID
NID_issuer_alt_name = MkNID 86

public export
NID_basic_constraints : NID
NID_basic_constraints = MkNID 87

public export
NID_crl_number : NID
NID_crl_number = MkNID 88

public export
NID_certificate_policies : NID
NID_certificate_policies = MkNID 89

public export
NID_authority_key_identifier : NID
NID_authority_key_identifier = MkNID 90

public export
NID_bf_cbc : NID
NID_bf_cbc = MkNID 91

public export
NID_bf_ecb : NID
NID_bf_ecb = MkNID 92

public export
NID_bf_cfb64 : NID
NID_bf_cfb64 = MkNID 93

public export
NID_bf_ofb64 : NID
NID_bf_ofb64 = MkNID 94

public export
NID_mdc2 : NID
NID_mdc2 = MkNID 95

public export
NID_mdc2WithRSA : NID
NID_mdc2WithRSA = MkNID 96

public export
NID_rc4_40 : NID
NID_rc4_40 = MkNID 97

public export
NID_rc2_40_cbc : NID
NID_rc2_40_cbc = MkNID 98

public export
NID_givenName : NID
NID_givenName = MkNID 99

public export
NID_surname : NID
NID_surname = MkNID 100

public export
NID_initials : NID
NID_initials = MkNID 101

public export
NID_uniqueIdentifier : NID
NID_uniqueIdentifier = MkNID 102

public export
NID_crl_distribution_points : NID
NID_crl_distribution_points = MkNID 103

public export
NID_md5WithRSA : NID
NID_md5WithRSA = MkNID 104

public export
NID_serialNumber : NID
NID_serialNumber = MkNID 105

public export
NID_title : NID
NID_title = MkNID 106

public export
NID_description : NID
NID_description = MkNID 107

public export
NID_cast5_cbc : NID
NID_cast5_cbc = MkNID 108

public export
NID_cast5_ecb : NID
NID_cast5_ecb = MkNID 109

public export
NID_cast5_cfb64 : NID
NID_cast5_cfb64 = MkNID 110

public export
NID_cast5_ofb64 : NID
NID_cast5_ofb64 = MkNID 111

public export
NID_pbeWithMD5AndCast5_CBC : NID
NID_pbeWithMD5AndCast5_CBC = MkNID 112

public export
NID_dsaWithSHA1 : NID
NID_dsaWithSHA1 = MkNID 113

public export
NID_md5_sha1 : NID
NID_md5_sha1 = MkNID 114

public export
NID_sha1WithRSA : NID
NID_sha1WithRSA = MkNID 115

public export
NID_dsa : NID
NID_dsa = MkNID 116

public export
NID_ripemd160 : NID
NID_ripemd160 = MkNID 117

public export
NID_ripemd160WithRSA : NID
NID_ripemd160WithRSA = MkNID 119

public export
NID_rc5_cbc : NID
NID_rc5_cbc = MkNID 120

public export
NID_rc5_ecb : NID
NID_rc5_ecb = MkNID 121

public export
NID_rc5_cfb64 : NID
NID_rc5_cfb64 = MkNID 122

public export
NID_rc5_ofb64 : NID
NID_rc5_ofb64 = MkNID 123

public export
NID_rle_compression : NID
NID_rle_compression = MkNID 124

public export
NID_zlib_compression : NID
NID_zlib_compression = MkNID 125

public export
NID_ext_key_usage : NID
NID_ext_key_usage = MkNID 126

public export
NID_id_pkix : NID
NID_id_pkix = MkNID 127

public export
NID_id_kp : NID
NID_id_kp = MkNID 128

public export
NID_server_auth : NID
NID_server_auth = MkNID 129

public export
NID_client_auth : NID
NID_client_auth = MkNID 130

public export
NID_code_sign : NID
NID_code_sign = MkNID 131

public export
NID_email_protect : NID
NID_email_protect = MkNID 132

public export
NID_time_stamp : NID
NID_time_stamp = MkNID 133

public export
NID_ms_code_ind : NID
NID_ms_code_ind = MkNID 134

public export
NID_ms_code_com : NID
NID_ms_code_com = MkNID 135

public export
NID_ms_ctl_sign : NID
NID_ms_ctl_sign = MkNID 136

public export
NID_ms_sgc : NID
NID_ms_sgc = MkNID 137

public export
NID_ms_efs : NID
NID_ms_efs = MkNID 138

public export
NID_ns_sgc : NID
NID_ns_sgc = MkNID 139

public export
NID_delta_crl : NID
NID_delta_crl = MkNID 140

public export
NID_crl_reason : NID
NID_crl_reason = MkNID 141

public export
NID_invalidity_date : NID
NID_invalidity_date = MkNID 142

public export
NID_sxnet : NID
NID_sxnet = MkNID 143

public export
NID_pbe_WithSHA1And128BitRC4 : NID
NID_pbe_WithSHA1And128BitRC4 = MkNID 144

public export
NID_pbe_WithSHA1And40BitRC4 : NID
NID_pbe_WithSHA1And40BitRC4 = MkNID 145

public export
NID_pbe_WithSHA1And3_Key_TripleDES_CBC : NID
NID_pbe_WithSHA1And3_Key_TripleDES_CBC = MkNID 146

public export
NID_pbe_WithSHA1And2_Key_TripleDES_CBC : NID
NID_pbe_WithSHA1And2_Key_TripleDES_CBC = MkNID 147

public export
NID_pbe_WithSHA1And128BitRC2_CBC : NID
NID_pbe_WithSHA1And128BitRC2_CBC = MkNID 148

public export
NID_pbe_WithSHA1And40BitRC2_CBC : NID
NID_pbe_WithSHA1And40BitRC2_CBC = MkNID 149

public export
NID_keyBag : NID
NID_keyBag = MkNID 150

public export
NID_pkcs8ShroudedKeyBag : NID
NID_pkcs8ShroudedKeyBag = MkNID 151

public export
NID_certBag : NID
NID_certBag = MkNID 152

public export
NID_crlBag : NID
NID_crlBag = MkNID 153

public export
NID_secretBag : NID
NID_secretBag = MkNID 154

public export
NID_safeContentsBag : NID
NID_safeContentsBag = MkNID 155

public export
NID_friendlyName : NID
NID_friendlyName = MkNID 156

public export
NID_localKeyID : NID
NID_localKeyID = MkNID 157

public export
NID_x509Certificate : NID
NID_x509Certificate = MkNID 158

public export
NID_sdsiCertificate : NID
NID_sdsiCertificate = MkNID 159

public export
NID_x509Crl : NID
NID_x509Crl = MkNID 160

public export
NID_pbes2 : NID
NID_pbes2 = MkNID 161

public export
NID_pbmac1 : NID
NID_pbmac1 = MkNID 162

public export
NID_hmacWithSHA1 : NID
NID_hmacWithSHA1 = MkNID 163

public export
NID_id_qt_cps : NID
NID_id_qt_cps = MkNID 164

public export
NID_id_qt_unotice : NID
NID_id_qt_unotice = MkNID 165

public export
NID_rc2_64_cbc : NID
NID_rc2_64_cbc = MkNID 166

public export
NID_SMIMECapabilities : NID
NID_SMIMECapabilities = MkNID 167

public export
NID_pbeWithMD2AndRC2_CBC : NID
NID_pbeWithMD2AndRC2_CBC = MkNID 168

public export
NID_pbeWithMD5AndRC2_CBC : NID
NID_pbeWithMD5AndRC2_CBC = MkNID 169

public export
NID_pbeWithSHA1AndDES_CBC : NID
NID_pbeWithSHA1AndDES_CBC = MkNID 170

public export
NID_ms_ext_req : NID
NID_ms_ext_req = MkNID 171

public export
NID_ext_req : NID
NID_ext_req = MkNID 172

public export
NID_name : NID
NID_name = MkNID 173

public export
NID_dnQualifier : NID
NID_dnQualifier = MkNID 174

public export
NID_id_pe : NID
NID_id_pe = MkNID 175

public export
NID_id_ad : NID
NID_id_ad = MkNID 176

public export
NID_info_access : NID
NID_info_access = MkNID 177

public export
NID_ad_OCSP : NID
NID_ad_OCSP = MkNID 178

public export
NID_ad_ca_issuers : NID
NID_ad_ca_issuers = MkNID 179

public export
NID_OCSP_sign : NID
NID_OCSP_sign = MkNID 180

public export
NID_iso : NID
NID_iso = MkNID 181

public export
NID_member_body : NID
NID_member_body = MkNID 182

public export
NID_ISO_US : NID
NID_ISO_US = MkNID 183

public export
NID_X9_57 : NID
NID_X9_57 = MkNID 184

public export
NID_X9cm : NID
NID_X9cm = MkNID 185

public export
NID_pkcs1 : NID
NID_pkcs1 = MkNID 186

public export
NID_pkcs5 : NID
NID_pkcs5 = MkNID 187

public export
NID_SMIME : NID
NID_SMIME = MkNID 188

public export
NID_id_smime_mod : NID
NID_id_smime_mod = MkNID 189

public export
NID_id_smime_ct : NID
NID_id_smime_ct = MkNID 190

public export
NID_id_smime_aa : NID
NID_id_smime_aa = MkNID 191

public export
NID_id_smime_alg : NID
NID_id_smime_alg = MkNID 192

public export
NID_id_smime_cd : NID
NID_id_smime_cd = MkNID 193

public export
NID_id_smime_spq : NID
NID_id_smime_spq = MkNID 194

public export
NID_id_smime_cti : NID
NID_id_smime_cti = MkNID 195

public export
NID_id_smime_mod_cms : NID
NID_id_smime_mod_cms = MkNID 196

public export
NID_id_smime_mod_ess : NID
NID_id_smime_mod_ess = MkNID 197

public export
NID_id_smime_mod_oid : NID
NID_id_smime_mod_oid = MkNID 198

public export
NID_id_smime_mod_msg_v3 : NID
NID_id_smime_mod_msg_v3 = MkNID 199

public export
NID_id_smime_mod_ets_eSignature_88 : NID
NID_id_smime_mod_ets_eSignature_88 = MkNID 200

public export
NID_id_smime_mod_ets_eSignature_97 : NID
NID_id_smime_mod_ets_eSignature_97 = MkNID 201

public export
NID_id_smime_mod_ets_eSigPolicy_88 : NID
NID_id_smime_mod_ets_eSigPolicy_88 = MkNID 202

public export
NID_id_smime_mod_ets_eSigPolicy_97 : NID
NID_id_smime_mod_ets_eSigPolicy_97 = MkNID 203

public export
NID_id_smime_ct_receipt : NID
NID_id_smime_ct_receipt = MkNID 204

public export
NID_id_smime_ct_authData : NID
NID_id_smime_ct_authData = MkNID 205

public export
NID_id_smime_ct_publishCert : NID
NID_id_smime_ct_publishCert = MkNID 206

public export
NID_id_smime_ct_TSTInfo : NID
NID_id_smime_ct_TSTInfo = MkNID 207

public export
NID_id_smime_ct_TDTInfo : NID
NID_id_smime_ct_TDTInfo = MkNID 208

public export
NID_id_smime_ct_contentInfo : NID
NID_id_smime_ct_contentInfo = MkNID 209

public export
NID_id_smime_ct_DVCSRequestData : NID
NID_id_smime_ct_DVCSRequestData = MkNID 210

public export
NID_id_smime_ct_DVCSResponseData : NID
NID_id_smime_ct_DVCSResponseData = MkNID 211

public export
NID_id_smime_aa_receiptRequest : NID
NID_id_smime_aa_receiptRequest = MkNID 212

public export
NID_id_smime_aa_securityLabel : NID
NID_id_smime_aa_securityLabel = MkNID 213

public export
NID_id_smime_aa_mlExpandHistory : NID
NID_id_smime_aa_mlExpandHistory = MkNID 214

public export
NID_id_smime_aa_contentHint : NID
NID_id_smime_aa_contentHint = MkNID 215

public export
NID_id_smime_aa_msgSigDigest : NID
NID_id_smime_aa_msgSigDigest = MkNID 216

public export
NID_id_smime_aa_encapContentType : NID
NID_id_smime_aa_encapContentType = MkNID 217

public export
NID_id_smime_aa_contentIdentifier : NID
NID_id_smime_aa_contentIdentifier = MkNID 218

public export
NID_id_smime_aa_macValue : NID
NID_id_smime_aa_macValue = MkNID 219

public export
NID_id_smime_aa_equivalentLabels : NID
NID_id_smime_aa_equivalentLabels = MkNID 220

public export
NID_id_smime_aa_contentReference : NID
NID_id_smime_aa_contentReference = MkNID 221

public export
NID_id_smime_aa_encrypKeyPref : NID
NID_id_smime_aa_encrypKeyPref = MkNID 222

public export
NID_id_smime_aa_signingCertificate : NID
NID_id_smime_aa_signingCertificate = MkNID 223

public export
NID_id_smime_aa_smimeEncryptCerts : NID
NID_id_smime_aa_smimeEncryptCerts = MkNID 224

public export
NID_id_smime_aa_timeStampToken : NID
NID_id_smime_aa_timeStampToken = MkNID 225

public export
NID_id_smime_aa_ets_sigPolicyId : NID
NID_id_smime_aa_ets_sigPolicyId = MkNID 226

public export
NID_id_smime_aa_ets_commitmentType : NID
NID_id_smime_aa_ets_commitmentType = MkNID 227

public export
NID_id_smime_aa_ets_signerLocation : NID
NID_id_smime_aa_ets_signerLocation = MkNID 228

public export
NID_id_smime_aa_ets_signerAttr : NID
NID_id_smime_aa_ets_signerAttr = MkNID 229

public export
NID_id_smime_aa_ets_otherSigCert : NID
NID_id_smime_aa_ets_otherSigCert = MkNID 230

public export
NID_id_smime_aa_ets_contentTimestamp : NID
NID_id_smime_aa_ets_contentTimestamp = MkNID 231

public export
NID_id_smime_aa_ets_CertificateRefs : NID
NID_id_smime_aa_ets_CertificateRefs = MkNID 232

public export
NID_id_smime_aa_ets_RevocationRefs : NID
NID_id_smime_aa_ets_RevocationRefs = MkNID 233

public export
NID_id_smime_aa_ets_certValues : NID
NID_id_smime_aa_ets_certValues = MkNID 234

public export
NID_id_smime_aa_ets_revocationValues : NID
NID_id_smime_aa_ets_revocationValues = MkNID 235

public export
NID_id_smime_aa_ets_escTimeStamp : NID
NID_id_smime_aa_ets_escTimeStamp = MkNID 236

public export
NID_id_smime_aa_ets_certCRLTimestamp : NID
NID_id_smime_aa_ets_certCRLTimestamp = MkNID 237

public export
NID_id_smime_aa_ets_archiveTimeStamp : NID
NID_id_smime_aa_ets_archiveTimeStamp = MkNID 238

public export
NID_id_smime_aa_signatureType : NID
NID_id_smime_aa_signatureType = MkNID 239

public export
NID_id_smime_aa_dvcs_dvc : NID
NID_id_smime_aa_dvcs_dvc = MkNID 240

public export
NID_id_smime_alg_ESDHwith3DES : NID
NID_id_smime_alg_ESDHwith3DES = MkNID 241

public export
NID_id_smime_alg_ESDHwithRC2 : NID
NID_id_smime_alg_ESDHwithRC2 = MkNID 242

public export
NID_id_smime_alg_3DESwrap : NID
NID_id_smime_alg_3DESwrap = MkNID 243

public export
NID_id_smime_alg_RC2wrap : NID
NID_id_smime_alg_RC2wrap = MkNID 244

public export
NID_id_smime_alg_ESDH : NID
NID_id_smime_alg_ESDH = MkNID 245

public export
NID_id_smime_alg_CMS3DESwrap : NID
NID_id_smime_alg_CMS3DESwrap = MkNID 246

public export
NID_id_smime_alg_CMSRC2wrap : NID
NID_id_smime_alg_CMSRC2wrap = MkNID 247

public export
NID_id_smime_cd_ldap : NID
NID_id_smime_cd_ldap = MkNID 248

public export
NID_id_smime_spq_ets_sqt_uri : NID
NID_id_smime_spq_ets_sqt_uri = MkNID 249

public export
NID_id_smime_spq_ets_sqt_unotice : NID
NID_id_smime_spq_ets_sqt_unotice = MkNID 250

public export
NID_id_smime_cti_ets_proofOfOrigin : NID
NID_id_smime_cti_ets_proofOfOrigin = MkNID 251

public export
NID_id_smime_cti_ets_proofOfReceipt : NID
NID_id_smime_cti_ets_proofOfReceipt = MkNID 252

public export
NID_id_smime_cti_ets_proofOfDelivery : NID
NID_id_smime_cti_ets_proofOfDelivery = MkNID 253

public export
NID_id_smime_cti_ets_proofOfSender : NID
NID_id_smime_cti_ets_proofOfSender = MkNID 254

public export
NID_id_smime_cti_ets_proofOfApproval : NID
NID_id_smime_cti_ets_proofOfApproval = MkNID 255

public export
NID_id_smime_cti_ets_proofOfCreation : NID
NID_id_smime_cti_ets_proofOfCreation = MkNID 256

public export
NID_md4 : NID
NID_md4 = MkNID 257

public export
NID_id_pkix_mod : NID
NID_id_pkix_mod = MkNID 258

public export
NID_id_qt : NID
NID_id_qt = MkNID 259

public export
NID_id_it : NID
NID_id_it = MkNID 260

public export
NID_id_pkip : NID
NID_id_pkip = MkNID 261

public export
NID_id_alg : NID
NID_id_alg = MkNID 262

public export
NID_id_cmc : NID
NID_id_cmc = MkNID 263

public export
NID_id_on : NID
NID_id_on = MkNID 264

public export
NID_id_pda : NID
NID_id_pda = MkNID 265

public export
NID_id_aca : NID
NID_id_aca = MkNID 266

public export
NID_id_qcs : NID
NID_id_qcs = MkNID 267

public export
NID_id_cct : NID
NID_id_cct = MkNID 268

public export
NID_id_pkix1_explicit_88 : NID
NID_id_pkix1_explicit_88 = MkNID 269

public export
NID_id_pkix1_implicit_88 : NID
NID_id_pkix1_implicit_88 = MkNID 270

public export
NID_id_pkix1_explicit_93 : NID
NID_id_pkix1_explicit_93 = MkNID 271

public export
NID_id_pkix1_implicit_93 : NID
NID_id_pkix1_implicit_93 = MkNID 272

public export
NID_id_mod_crmf : NID
NID_id_mod_crmf = MkNID 273

public export
NID_id_mod_cmc : NID
NID_id_mod_cmc = MkNID 274

public export
NID_id_mod_kea_profile_88 : NID
NID_id_mod_kea_profile_88 = MkNID 275

public export
NID_id_mod_kea_profile_93 : NID
NID_id_mod_kea_profile_93 = MkNID 276

public export
NID_id_mod_cmp : NID
NID_id_mod_cmp = MkNID 277

public export
NID_id_mod_qualified_cert_88 : NID
NID_id_mod_qualified_cert_88 = MkNID 278

public export
NID_id_mod_qualified_cert_93 : NID
NID_id_mod_qualified_cert_93 = MkNID 279

public export
NID_id_mod_attribute_cert : NID
NID_id_mod_attribute_cert = MkNID 280

public export
NID_id_mod_timestamp_protocol : NID
NID_id_mod_timestamp_protocol = MkNID 281

public export
NID_id_mod_ocsp : NID
NID_id_mod_ocsp = MkNID 282

public export
NID_id_mod_dvcs : NID
NID_id_mod_dvcs = MkNID 283

public export
NID_id_mod_cmp2000 : NID
NID_id_mod_cmp2000 = MkNID 284

public export
NID_biometricInfo : NID
NID_biometricInfo = MkNID 285

public export
NID_qcStatements : NID
NID_qcStatements = MkNID 286

public export
NID_ac_auditEntity : NID
NID_ac_auditEntity = MkNID 287

public export
NID_ac_targeting : NID
NID_ac_targeting = MkNID 288

public export
NID_aaControls : NID
NID_aaControls = MkNID 289

public export
NID_sbgp_ipAddrBlock : NID
NID_sbgp_ipAddrBlock = MkNID 290

public export
NID_sbgp_autonomousSysNum : NID
NID_sbgp_autonomousSysNum = MkNID 291

public export
NID_sbgp_routerIdentifier : NID
NID_sbgp_routerIdentifier = MkNID 292

public export
NID_textNotice : NID
NID_textNotice = MkNID 293

public export
NID_ipsecEndSystem : NID
NID_ipsecEndSystem = MkNID 294

public export
NID_ipsecTunnel : NID
NID_ipsecTunnel = MkNID 295

public export
NID_ipsecUser : NID
NID_ipsecUser = MkNID 296

public export
NID_dvcs : NID
NID_dvcs = MkNID 297

public export
NID_id_it_caProtEncCert : NID
NID_id_it_caProtEncCert = MkNID 298

public export
NID_id_it_signKeyPairTypes : NID
NID_id_it_signKeyPairTypes = MkNID 299

public export
NID_id_it_encKeyPairTypes : NID
NID_id_it_encKeyPairTypes = MkNID 300

public export
NID_id_it_preferredSymmAlg : NID
NID_id_it_preferredSymmAlg = MkNID 301

public export
NID_id_it_caKeyUpdateInfo : NID
NID_id_it_caKeyUpdateInfo = MkNID 302

public export
NID_id_it_currentCRL : NID
NID_id_it_currentCRL = MkNID 303

public export
NID_id_it_unsupportedOIDs : NID
NID_id_it_unsupportedOIDs = MkNID 304

public export
NID_id_it_subscriptionRequest : NID
NID_id_it_subscriptionRequest = MkNID 305

public export
NID_id_it_subscriptionResponse : NID
NID_id_it_subscriptionResponse = MkNID 306

public export
NID_id_it_keyPairParamReq : NID
NID_id_it_keyPairParamReq = MkNID 307

public export
NID_id_it_keyPairParamRep : NID
NID_id_it_keyPairParamRep = MkNID 308

public export
NID_id_it_revPassphrase : NID
NID_id_it_revPassphrase = MkNID 309

public export
NID_id_it_implicitConfirm : NID
NID_id_it_implicitConfirm = MkNID 310

public export
NID_id_it_confirmWaitTime : NID
NID_id_it_confirmWaitTime = MkNID 311

public export
NID_id_it_origPKIMessage : NID
NID_id_it_origPKIMessage = MkNID 312

public export
NID_id_regCtrl : NID
NID_id_regCtrl = MkNID 313

public export
NID_id_regInfo : NID
NID_id_regInfo = MkNID 314

public export
NID_id_regCtrl_regToken : NID
NID_id_regCtrl_regToken = MkNID 315

public export
NID_id_regCtrl_authenticator : NID
NID_id_regCtrl_authenticator = MkNID 316

public export
NID_id_regCtrl_pkiPublicationInfo : NID
NID_id_regCtrl_pkiPublicationInfo = MkNID 317

public export
NID_id_regCtrl_pkiArchiveOptions : NID
NID_id_regCtrl_pkiArchiveOptions = MkNID 318

public export
NID_id_regCtrl_oldCertID : NID
NID_id_regCtrl_oldCertID = MkNID 319

public export
NID_id_regCtrl_protocolEncrKey : NID
NID_id_regCtrl_protocolEncrKey = MkNID 320

public export
NID_id_regInfo_utf8Pairs : NID
NID_id_regInfo_utf8Pairs = MkNID 321

public export
NID_id_regInfo_certReq : NID
NID_id_regInfo_certReq = MkNID 322

public export
NID_id_alg_des40 : NID
NID_id_alg_des40 = MkNID 323

public export
NID_id_alg_noSignature : NID
NID_id_alg_noSignature = MkNID 324

public export
NID_id_alg_dh_sig_hmac_sha1 : NID
NID_id_alg_dh_sig_hmac_sha1 = MkNID 325

public export
NID_id_alg_dh_pop : NID
NID_id_alg_dh_pop = MkNID 326

public export
NID_id_cmc_statusInfo : NID
NID_id_cmc_statusInfo = MkNID 327

public export
NID_id_cmc_identification : NID
NID_id_cmc_identification = MkNID 328

public export
NID_id_cmc_identityProof : NID
NID_id_cmc_identityProof = MkNID 329

public export
NID_id_cmc_dataReturn : NID
NID_id_cmc_dataReturn = MkNID 330

public export
NID_id_cmc_transactionId : NID
NID_id_cmc_transactionId = MkNID 331

public export
NID_id_cmc_senderNonce : NID
NID_id_cmc_senderNonce = MkNID 332

public export
NID_id_cmc_recipientNonce : NID
NID_id_cmc_recipientNonce = MkNID 333

public export
NID_id_cmc_addExtensions : NID
NID_id_cmc_addExtensions = MkNID 334

public export
NID_id_cmc_encryptedPOP : NID
NID_id_cmc_encryptedPOP = MkNID 335

public export
NID_id_cmc_decryptedPOP : NID
NID_id_cmc_decryptedPOP = MkNID 336

public export
NID_id_cmc_lraPOPWitness : NID
NID_id_cmc_lraPOPWitness = MkNID 337

public export
NID_id_cmc_getCert : NID
NID_id_cmc_getCert = MkNID 338

public export
NID_id_cmc_getCRL : NID
NID_id_cmc_getCRL = MkNID 339

public export
NID_id_cmc_revokeRequest : NID
NID_id_cmc_revokeRequest = MkNID 340

public export
NID_id_cmc_regInfo : NID
NID_id_cmc_regInfo = MkNID 341

public export
NID_id_cmc_responseInfo : NID
NID_id_cmc_responseInfo = MkNID 342

public export
NID_id_cmc_queryPending : NID
NID_id_cmc_queryPending = MkNID 343

public export
NID_id_cmc_popLinkRandom : NID
NID_id_cmc_popLinkRandom = MkNID 344

public export
NID_id_cmc_popLinkWitness : NID
NID_id_cmc_popLinkWitness = MkNID 345

public export
NID_id_cmc_confirmCertAcceptance : NID
NID_id_cmc_confirmCertAcceptance = MkNID 346

public export
NID_id_on_personalData : NID
NID_id_on_personalData = MkNID 347

public export
NID_id_pda_dateOfBirth : NID
NID_id_pda_dateOfBirth = MkNID 348

public export
NID_id_pda_placeOfBirth : NID
NID_id_pda_placeOfBirth = MkNID 349

public export
NID_id_pda_pseudonym : NID
NID_id_pda_pseudonym = MkNID 350

public export
NID_id_pda_gender : NID
NID_id_pda_gender = MkNID 351

public export
NID_id_pda_countryOfCitizenship : NID
NID_id_pda_countryOfCitizenship = MkNID 352

public export
NID_id_pda_countryOfResidence : NID
NID_id_pda_countryOfResidence = MkNID 353

public export
NID_id_aca_authenticationInfo : NID
NID_id_aca_authenticationInfo = MkNID 354

public export
NID_id_aca_accessIdentity : NID
NID_id_aca_accessIdentity = MkNID 355

public export
NID_id_aca_chargingIdentity : NID
NID_id_aca_chargingIdentity = MkNID 356

public export
NID_id_aca_group : NID
NID_id_aca_group = MkNID 357

public export
NID_id_aca_role : NID
NID_id_aca_role = MkNID 358

public export
NID_id_qcs_pkixQCSyntax_v1 : NID
NID_id_qcs_pkixQCSyntax_v1 = MkNID 359

public export
NID_id_cct_crs : NID
NID_id_cct_crs = MkNID 360

public export
NID_id_cct_PKIData : NID
NID_id_cct_PKIData = MkNID 361

public export
NID_id_cct_PKIResponse : NID
NID_id_cct_PKIResponse = MkNID 362

public export
NID_ad_timeStamping : NID
NID_ad_timeStamping = MkNID 363

public export
NID_ad_dvcs : NID
NID_ad_dvcs = MkNID 364

public export
NID_id_pkix_OCSP_basic : NID
NID_id_pkix_OCSP_basic = MkNID 365

public export
NID_id_pkix_OCSP_Nonce : NID
NID_id_pkix_OCSP_Nonce = MkNID 366

public export
NID_id_pkix_OCSP_CrlID : NID
NID_id_pkix_OCSP_CrlID = MkNID 367

public export
NID_id_pkix_OCSP_acceptableResponses : NID
NID_id_pkix_OCSP_acceptableResponses = MkNID 368

public export
NID_id_pkix_OCSP_noCheck : NID
NID_id_pkix_OCSP_noCheck = MkNID 369

public export
NID_id_pkix_OCSP_archiveCutoff : NID
NID_id_pkix_OCSP_archiveCutoff = MkNID 370

public export
NID_id_pkix_OCSP_serviceLocator : NID
NID_id_pkix_OCSP_serviceLocator = MkNID 371

public export
NID_id_pkix_OCSP_extendedStatus : NID
NID_id_pkix_OCSP_extendedStatus = MkNID 372

public export
NID_id_pkix_OCSP_valid : NID
NID_id_pkix_OCSP_valid = MkNID 373

public export
NID_id_pkix_OCSP_path : NID
NID_id_pkix_OCSP_path = MkNID 374

public export
NID_id_pkix_OCSP_trustRoot : NID
NID_id_pkix_OCSP_trustRoot = MkNID 375

public export
NID_algorithm : NID
NID_algorithm = MkNID 376

public export
NID_rsaSignature : NID
NID_rsaSignature = MkNID 377

public export
NID_X500algorithms : NID
NID_X500algorithms = MkNID 378

public export
NID_org : NID
NID_org = MkNID 379

public export
NID_dod : NID
NID_dod = MkNID 380

public export
NID_iana : NID
NID_iana = MkNID 381

public export
NID_Directory : NID
NID_Directory = MkNID 382

public export
NID_Management : NID
NID_Management = MkNID 383

public export
NID_Experimental : NID
NID_Experimental = MkNID 384

public export
NID_Private : NID
NID_Private = MkNID 385

public export
NID_Security : NID
NID_Security = MkNID 386

public export
NID_SNMPv2 : NID
NID_SNMPv2 = MkNID 387

public export
NID_Mail : NID
NID_Mail = MkNID 388

public export
NID_Enterprises : NID
NID_Enterprises = MkNID 389

public export
NID_dcObject : NID
NID_dcObject = MkNID 390

public export
NID_domainComponent : NID
NID_domainComponent = MkNID 391

public export
NID_Domain : NID
NID_Domain = MkNID 392

public export
NID_joint_iso_ccitt : NID
NID_joint_iso_ccitt = MkNID 393

public export
NID_selected_attribute_types : NID
NID_selected_attribute_types = MkNID 394

public export
NID_clearance : NID
NID_clearance = MkNID 395

public export
NID_md4WithRSAEncryption : NID
NID_md4WithRSAEncryption = MkNID 396

public export
NID_ac_proxying : NID
NID_ac_proxying = MkNID 397

public export
NID_sinfo_access : NID
NID_sinfo_access = MkNID 398

public export
NID_id_aca_encAttrs : NID
NID_id_aca_encAttrs = MkNID 399

public export
NID_role : NID
NID_role = MkNID 400

public export
NID_policy_constraints : NID
NID_policy_constraints = MkNID 401

public export
NID_target_information : NID
NID_target_information = MkNID 402

public export
NID_no_rev_avail : NID
NID_no_rev_avail = MkNID 403

public export
NID_ccitt : NID
NID_ccitt = MkNID 404

public export
NID_ansi_X9_62 : NID
NID_ansi_X9_62 = MkNID 405

public export
NID_X9_62_prime_field : NID
NID_X9_62_prime_field = MkNID 406

public export
NID_X9_62_characteristic_two_field : NID
NID_X9_62_characteristic_two_field = MkNID 407

public export
NID_X9_62_id_ecPublicKey : NID
NID_X9_62_id_ecPublicKey = MkNID 408

public export
NID_X9_62_prime192v1 : NID
NID_X9_62_prime192v1 = MkNID 409

public export
NID_X9_62_prime192v2 : NID
NID_X9_62_prime192v2 = MkNID 410

public export
NID_X9_62_prime192v3 : NID
NID_X9_62_prime192v3 = MkNID 411

public export
NID_X9_62_prime239v1 : NID
NID_X9_62_prime239v1 = MkNID 412

public export
NID_X9_62_prime239v2 : NID
NID_X9_62_prime239v2 = MkNID 413

public export
NID_X9_62_prime239v3 : NID
NID_X9_62_prime239v3 = MkNID 414

public export
NID_X9_62_prime256v1 : NID
NID_X9_62_prime256v1 = MkNID 415

public export
NID_ecdsa_with_SHA1 : NID
NID_ecdsa_with_SHA1 = MkNID 416

public export
NID_ms_csp_name : NID
NID_ms_csp_name = MkNID 417

public export
NID_aes_128_ecb : NID
NID_aes_128_ecb = MkNID 418

public export
NID_aes_128_cbc : NID
NID_aes_128_cbc = MkNID 419

public export
NID_aes_128_ofb128 : NID
NID_aes_128_ofb128 = MkNID 420

public export
NID_aes_128_cfb128 : NID
NID_aes_128_cfb128 = MkNID 421

public export
NID_aes_192_ecb : NID
NID_aes_192_ecb = MkNID 422

public export
NID_aes_192_cbc : NID
NID_aes_192_cbc = MkNID 423

public export
NID_aes_192_ofb128 : NID
NID_aes_192_ofb128 = MkNID 424

public export
NID_aes_192_cfb128 : NID
NID_aes_192_cfb128 = MkNID 425

public export
NID_aes_256_ecb : NID
NID_aes_256_ecb = MkNID 426

public export
NID_aes_256_cbc : NID
NID_aes_256_cbc = MkNID 427

public export
NID_aes_256_ofb128 : NID
NID_aes_256_ofb128 = MkNID 428

public export
NID_aes_256_cfb128 : NID
NID_aes_256_cfb128 = MkNID 429

public export
NID_hold_instruction_code : NID
NID_hold_instruction_code = MkNID 430

public export
NID_hold_instruction_none : NID
NID_hold_instruction_none = MkNID 431

public export
NID_hold_instruction_call_issuer : NID
NID_hold_instruction_call_issuer = MkNID 432

public export
NID_hold_instruction_reject : NID
NID_hold_instruction_reject = MkNID 433

public export
NID_data : NID
NID_data = MkNID 434

public export
NID_pss : NID
NID_pss = MkNID 435

public export
NID_ucl : NID
NID_ucl = MkNID 436

public export
NID_pilot : NID
NID_pilot = MkNID 437

public export
NID_pilotAttributeType : NID
NID_pilotAttributeType = MkNID 438

public export
NID_pilotAttributeSyntax : NID
NID_pilotAttributeSyntax = MkNID 439

public export
NID_pilotObjectClass : NID
NID_pilotObjectClass = MkNID 440

public export
NID_pilotGroups : NID
NID_pilotGroups = MkNID 441

public export
NID_iA5StringSyntax : NID
NID_iA5StringSyntax = MkNID 442

public export
NID_caseIgnoreIA5StringSyntax : NID
NID_caseIgnoreIA5StringSyntax = MkNID 443

public export
NID_pilotObject : NID
NID_pilotObject = MkNID 444

public export
NID_pilotPerson : NID
NID_pilotPerson = MkNID 445

public export
NID_account : NID
NID_account = MkNID 446

public export
NID_document : NID
NID_document = MkNID 447

public export
NID_room : NID
NID_room = MkNID 448

public export
NID_documentSeries : NID
NID_documentSeries = MkNID 449

public export
NID_rFC822localPart : NID
NID_rFC822localPart = MkNID 450

public export
NID_dNSDomain : NID
NID_dNSDomain = MkNID 451

public export
NID_domainRelatedObject : NID
NID_domainRelatedObject = MkNID 452

public export
NID_friendlyCountry : NID
NID_friendlyCountry = MkNID 453

public export
NID_simpleSecurityObject : NID
NID_simpleSecurityObject = MkNID 454

public export
NID_pilotOrganization : NID
NID_pilotOrganization = MkNID 455

public export
NID_pilotDSA : NID
NID_pilotDSA = MkNID 456

public export
NID_qualityLabelledData : NID
NID_qualityLabelledData = MkNID 457

public export
NID_userId : NID
NID_userId = MkNID 458

public export
NID_textEncodedORAddress : NID
NID_textEncodedORAddress = MkNID 459

public export
NID_rfc822Mailbox : NID
NID_rfc822Mailbox = MkNID 460

public export
NID_info : NID
NID_info = MkNID 461

public export
NID_favouriteDrink : NID
NID_favouriteDrink = MkNID 462

public export
NID_roomNumber : NID
NID_roomNumber = MkNID 463

public export
NID_photo : NID
NID_photo = MkNID 464

public export
NID_userClass : NID
NID_userClass = MkNID 465

public export
NID_host : NID
NID_host = MkNID 466

public export
NID_manager : NID
NID_manager = MkNID 467

public export
NID_documentIdentifier : NID
NID_documentIdentifier = MkNID 468

public export
NID_documentTitle : NID
NID_documentTitle = MkNID 469

public export
NID_documentVersion : NID
NID_documentVersion = MkNID 470

public export
NID_documentAuthor : NID
NID_documentAuthor = MkNID 471

public export
NID_documentLocation : NID
NID_documentLocation = MkNID 472

public export
NID_homeTelephoneNumber : NID
NID_homeTelephoneNumber = MkNID 473

public export
NID_secretary : NID
NID_secretary = MkNID 474

public export
NID_otherMailbox : NID
NID_otherMailbox = MkNID 475

public export
NID_lastModifiedTime : NID
NID_lastModifiedTime = MkNID 476

public export
NID_lastModifiedBy : NID
NID_lastModifiedBy = MkNID 477

public export
NID_aRecord : NID
NID_aRecord = MkNID 478

public export
NID_pilotAttributeType27 : NID
NID_pilotAttributeType27 = MkNID 479

public export
NID_mXRecord : NID
NID_mXRecord = MkNID 480

public export
NID_nSRecord : NID
NID_nSRecord = MkNID 481

public export
NID_sOARecord : NID
NID_sOARecord = MkNID 482

public export
NID_cNAMERecord : NID
NID_cNAMERecord = MkNID 483

public export
NID_associatedDomain : NID
NID_associatedDomain = MkNID 484

public export
NID_associatedName : NID
NID_associatedName = MkNID 485

public export
NID_homePostalAddress : NID
NID_homePostalAddress = MkNID 486

public export
NID_personalTitle : NID
NID_personalTitle = MkNID 487

public export
NID_mobileTelephoneNumber : NID
NID_mobileTelephoneNumber = MkNID 488

public export
NID_pagerTelephoneNumber : NID
NID_pagerTelephoneNumber = MkNID 489

public export
NID_friendlyCountryName : NID
NID_friendlyCountryName = MkNID 490

public export
NID_organizationalStatus : NID
NID_organizationalStatus = MkNID 491

public export
NID_janetMailbox : NID
NID_janetMailbox = MkNID 492

public export
NID_mailPreferenceOption : NID
NID_mailPreferenceOption = MkNID 493

public export
NID_buildingName : NID
NID_buildingName = MkNID 494

public export
NID_dSAQuality : NID
NID_dSAQuality = MkNID 495

public export
NID_singleLevelQuality : NID
NID_singleLevelQuality = MkNID 496

public export
NID_subtreeMinimumQuality : NID
NID_subtreeMinimumQuality = MkNID 497

public export
NID_subtreeMaximumQuality : NID
NID_subtreeMaximumQuality = MkNID 498

public export
NID_personalSignature : NID
NID_personalSignature = MkNID 499

public export
NID_dITRedirect : NID
NID_dITRedirect = MkNID 500

public export
NID_audio : NID
NID_audio = MkNID 501

public export
NID_documentPublisher : NID
NID_documentPublisher = MkNID 502

public export
NID_x500UniqueIdentifier : NID
NID_x500UniqueIdentifier = MkNID 503

public export
NID_mime_mhs : NID
NID_mime_mhs = MkNID 504

public export
NID_mime_mhs_headings : NID
NID_mime_mhs_headings = MkNID 505

public export
NID_mime_mhs_bodies : NID
NID_mime_mhs_bodies = MkNID 506

public export
NID_id_hex_partial_message : NID
NID_id_hex_partial_message = MkNID 507

public export
NID_id_hex_multipart_message : NID
NID_id_hex_multipart_message = MkNID 508

public export
NID_generationQualifier : NID
NID_generationQualifier = MkNID 509

public export
NID_pseudonym : NID
NID_pseudonym = MkNID 510

public export
NID_InternationalRA : NID
NID_InternationalRA = MkNID 511

public export
NID_id_set : NID
NID_id_set = MkNID 512

public export
NID_set_ctype : NID
NID_set_ctype = MkNID 513

public export
NID_set_msgExt : NID
NID_set_msgExt = MkNID 514

public export
NID_set_attr : NID
NID_set_attr = MkNID 515

public export
NID_set_policy : NID
NID_set_policy = MkNID 516

public export
NID_set_certExt : NID
NID_set_certExt = MkNID 517

public export
NID_set_brand : NID
NID_set_brand = MkNID 518

public export
NID_setct_PANData : NID
NID_setct_PANData = MkNID 519

public export
NID_setct_PANToken : NID
NID_setct_PANToken = MkNID 520

public export
NID_setct_PANOnly : NID
NID_setct_PANOnly = MkNID 521

public export
NID_setct_OIData : NID
NID_setct_OIData = MkNID 522

public export
NID_setct_PI : NID
NID_setct_PI = MkNID 523

public export
NID_setct_PIData : NID
NID_setct_PIData = MkNID 524

public export
NID_setct_PIDataUnsigned : NID
NID_setct_PIDataUnsigned = MkNID 525

public export
NID_setct_HODInput : NID
NID_setct_HODInput = MkNID 526

public export
NID_setct_AuthResBaggage : NID
NID_setct_AuthResBaggage = MkNID 527

public export
NID_setct_AuthRevReqBaggage : NID
NID_setct_AuthRevReqBaggage = MkNID 528

public export
NID_setct_AuthRevResBaggage : NID
NID_setct_AuthRevResBaggage = MkNID 529

public export
NID_setct_CapTokenSeq : NID
NID_setct_CapTokenSeq = MkNID 530

public export
NID_setct_PInitResData : NID
NID_setct_PInitResData = MkNID 531

public export
NID_setct_PI_TBS : NID
NID_setct_PI_TBS = MkNID 532

public export
NID_setct_PResData : NID
NID_setct_PResData = MkNID 533

public export
NID_setct_AuthReqTBS : NID
NID_setct_AuthReqTBS = MkNID 534

public export
NID_setct_AuthResTBS : NID
NID_setct_AuthResTBS = MkNID 535

public export
NID_setct_AuthResTBSX : NID
NID_setct_AuthResTBSX = MkNID 536

public export
NID_setct_AuthTokenTBS : NID
NID_setct_AuthTokenTBS = MkNID 537

public export
NID_setct_CapTokenData : NID
NID_setct_CapTokenData = MkNID 538

public export
NID_setct_CapTokenTBS : NID
NID_setct_CapTokenTBS = MkNID 539

public export
NID_setct_AcqCardCodeMsg : NID
NID_setct_AcqCardCodeMsg = MkNID 540

public export
NID_setct_AuthRevReqTBS : NID
NID_setct_AuthRevReqTBS = MkNID 541

public export
NID_setct_AuthRevResData : NID
NID_setct_AuthRevResData = MkNID 542

public export
NID_setct_AuthRevResTBS : NID
NID_setct_AuthRevResTBS = MkNID 543

public export
NID_setct_CapReqTBS : NID
NID_setct_CapReqTBS = MkNID 544

public export
NID_setct_CapReqTBSX : NID
NID_setct_CapReqTBSX = MkNID 545

public export
NID_setct_CapResData : NID
NID_setct_CapResData = MkNID 546

public export
NID_setct_CapRevReqTBS : NID
NID_setct_CapRevReqTBS = MkNID 547

public export
NID_setct_CapRevReqTBSX : NID
NID_setct_CapRevReqTBSX = MkNID 548

public export
NID_setct_CapRevResData : NID
NID_setct_CapRevResData = MkNID 549

public export
NID_setct_CredReqTBS : NID
NID_setct_CredReqTBS = MkNID 550

public export
NID_setct_CredReqTBSX : NID
NID_setct_CredReqTBSX = MkNID 551

public export
NID_setct_CredResData : NID
NID_setct_CredResData = MkNID 552

public export
NID_setct_CredRevReqTBS : NID
NID_setct_CredRevReqTBS = MkNID 553

public export
NID_setct_CredRevReqTBSX : NID
NID_setct_CredRevReqTBSX = MkNID 554

public export
NID_setct_CredRevResData : NID
NID_setct_CredRevResData = MkNID 555

public export
NID_setct_PCertReqData : NID
NID_setct_PCertReqData = MkNID 556

public export
NID_setct_PCertResTBS : NID
NID_setct_PCertResTBS = MkNID 557

public export
NID_setct_BatchAdminReqData : NID
NID_setct_BatchAdminReqData = MkNID 558

public export
NID_setct_BatchAdminResData : NID
NID_setct_BatchAdminResData = MkNID 559

public export
NID_setct_CardCInitResTBS : NID
NID_setct_CardCInitResTBS = MkNID 560

public export
NID_setct_MeAqCInitResTBS : NID
NID_setct_MeAqCInitResTBS = MkNID 561

public export
NID_setct_RegFormResTBS : NID
NID_setct_RegFormResTBS = MkNID 562

public export
NID_setct_CertReqData : NID
NID_setct_CertReqData = MkNID 563

public export
NID_setct_CertReqTBS : NID
NID_setct_CertReqTBS = MkNID 564

public export
NID_setct_CertResData : NID
NID_setct_CertResData = MkNID 565

public export
NID_setct_CertInqReqTBS : NID
NID_setct_CertInqReqTBS = MkNID 566

public export
NID_setct_ErrorTBS : NID
NID_setct_ErrorTBS = MkNID 567

public export
NID_setct_PIDualSignedTBE : NID
NID_setct_PIDualSignedTBE = MkNID 568

public export
NID_setct_PIUnsignedTBE : NID
NID_setct_PIUnsignedTBE = MkNID 569

public export
NID_setct_AuthReqTBE : NID
NID_setct_AuthReqTBE = MkNID 570

public export
NID_setct_AuthResTBE : NID
NID_setct_AuthResTBE = MkNID 571

public export
NID_setct_AuthResTBEX : NID
NID_setct_AuthResTBEX = MkNID 572

public export
NID_setct_AuthTokenTBE : NID
NID_setct_AuthTokenTBE = MkNID 573

public export
NID_setct_CapTokenTBE : NID
NID_setct_CapTokenTBE = MkNID 574

public export
NID_setct_CapTokenTBEX : NID
NID_setct_CapTokenTBEX = MkNID 575

public export
NID_setct_AcqCardCodeMsgTBE : NID
NID_setct_AcqCardCodeMsgTBE = MkNID 576

public export
NID_setct_AuthRevReqTBE : NID
NID_setct_AuthRevReqTBE = MkNID 577

public export
NID_setct_AuthRevResTBE : NID
NID_setct_AuthRevResTBE = MkNID 578

public export
NID_setct_AuthRevResTBEB : NID
NID_setct_AuthRevResTBEB = MkNID 579

public export
NID_setct_CapReqTBE : NID
NID_setct_CapReqTBE = MkNID 580

public export
NID_setct_CapReqTBEX : NID
NID_setct_CapReqTBEX = MkNID 581

public export
NID_setct_CapResTBE : NID
NID_setct_CapResTBE = MkNID 582

public export
NID_setct_CapRevReqTBE : NID
NID_setct_CapRevReqTBE = MkNID 583

public export
NID_setct_CapRevReqTBEX : NID
NID_setct_CapRevReqTBEX = MkNID 584

public export
NID_setct_CapRevResTBE : NID
NID_setct_CapRevResTBE = MkNID 585

public export
NID_setct_CredReqTBE : NID
NID_setct_CredReqTBE = MkNID 586

public export
NID_setct_CredReqTBEX : NID
NID_setct_CredReqTBEX = MkNID 587

public export
NID_setct_CredResTBE : NID
NID_setct_CredResTBE = MkNID 588

public export
NID_setct_CredRevReqTBE : NID
NID_setct_CredRevReqTBE = MkNID 589

public export
NID_setct_CredRevReqTBEX : NID
NID_setct_CredRevReqTBEX = MkNID 590

public export
NID_setct_CredRevResTBE : NID
NID_setct_CredRevResTBE = MkNID 591

public export
NID_setct_BatchAdminReqTBE : NID
NID_setct_BatchAdminReqTBE = MkNID 592

public export
NID_setct_BatchAdminResTBE : NID
NID_setct_BatchAdminResTBE = MkNID 593

public export
NID_setct_RegFormReqTBE : NID
NID_setct_RegFormReqTBE = MkNID 594

public export
NID_setct_CertReqTBE : NID
NID_setct_CertReqTBE = MkNID 595

public export
NID_setct_CertReqTBEX : NID
NID_setct_CertReqTBEX = MkNID 596

public export
NID_setct_CertResTBE : NID
NID_setct_CertResTBE = MkNID 597

public export
NID_setct_CRLNotificationTBS : NID
NID_setct_CRLNotificationTBS = MkNID 598

public export
NID_setct_CRLNotificationResTBS : NID
NID_setct_CRLNotificationResTBS = MkNID 599

public export
NID_setct_BCIDistributionTBS : NID
NID_setct_BCIDistributionTBS = MkNID 600

public export
NID_setext_genCrypt : NID
NID_setext_genCrypt = MkNID 601

public export
NID_setext_miAuth : NID
NID_setext_miAuth = MkNID 602

public export
NID_setext_pinSecure : NID
NID_setext_pinSecure = MkNID 603

public export
NID_setext_pinAny : NID
NID_setext_pinAny = MkNID 604

public export
NID_setext_track2 : NID
NID_setext_track2 = MkNID 605

public export
NID_setext_cv : NID
NID_setext_cv = MkNID 606

public export
NID_set_policy_root : NID
NID_set_policy_root = MkNID 607

public export
NID_setCext_hashedRoot : NID
NID_setCext_hashedRoot = MkNID 608

public export
NID_setCext_certType : NID
NID_setCext_certType = MkNID 609

public export
NID_setCext_merchData : NID
NID_setCext_merchData = MkNID 610

public export
NID_setCext_cCertRequired : NID
NID_setCext_cCertRequired = MkNID 611

public export
NID_setCext_tunneling : NID
NID_setCext_tunneling = MkNID 612

public export
NID_setCext_setExt : NID
NID_setCext_setExt = MkNID 613

public export
NID_setCext_setQualf : NID
NID_setCext_setQualf = MkNID 614

public export
NID_setCext_PGWYcapabilities : NID
NID_setCext_PGWYcapabilities = MkNID 615

public export
NID_setCext_TokenIdentifier : NID
NID_setCext_TokenIdentifier = MkNID 616

public export
NID_setCext_Track2Data : NID
NID_setCext_Track2Data = MkNID 617

public export
NID_setCext_TokenType : NID
NID_setCext_TokenType = MkNID 618

public export
NID_setCext_IssuerCapabilities : NID
NID_setCext_IssuerCapabilities = MkNID 619

public export
NID_setAttr_Cert : NID
NID_setAttr_Cert = MkNID 620

public export
NID_setAttr_PGWYcap : NID
NID_setAttr_PGWYcap = MkNID 621

public export
NID_setAttr_TokenType : NID
NID_setAttr_TokenType = MkNID 622

public export
NID_setAttr_IssCap : NID
NID_setAttr_IssCap = MkNID 623

public export
NID_set_rootKeyThumb : NID
NID_set_rootKeyThumb = MkNID 624

public export
NID_set_addPolicy : NID
NID_set_addPolicy = MkNID 625

public export
NID_setAttr_Token_EMV : NID
NID_setAttr_Token_EMV = MkNID 626

public export
NID_setAttr_Token_B0Prime : NID
NID_setAttr_Token_B0Prime = MkNID 627

public export
NID_setAttr_IssCap_CVM : NID
NID_setAttr_IssCap_CVM = MkNID 628

public export
NID_setAttr_IssCap_T2 : NID
NID_setAttr_IssCap_T2 = MkNID 629

public export
NID_setAttr_IssCap_Sig : NID
NID_setAttr_IssCap_Sig = MkNID 630

public export
NID_setAttr_GenCryptgrm : NID
NID_setAttr_GenCryptgrm = MkNID 631

public export
NID_setAttr_T2Enc : NID
NID_setAttr_T2Enc = MkNID 632

public export
NID_setAttr_T2cleartxt : NID
NID_setAttr_T2cleartxt = MkNID 633

public export
NID_setAttr_TokICCsig : NID
NID_setAttr_TokICCsig = MkNID 634

public export
NID_setAttr_SecDevSig : NID
NID_setAttr_SecDevSig = MkNID 635

public export
NID_set_brand_IATA_ATA : NID
NID_set_brand_IATA_ATA = MkNID 636

public export
NID_set_brand_Diners : NID
NID_set_brand_Diners = MkNID 637

public export
NID_set_brand_AmericanExpress : NID
NID_set_brand_AmericanExpress = MkNID 638

public export
NID_set_brand_JCB : NID
NID_set_brand_JCB = MkNID 639

public export
NID_set_brand_Visa : NID
NID_set_brand_Visa = MkNID 640

public export
NID_set_brand_MasterCard : NID
NID_set_brand_MasterCard = MkNID 641

public export
NID_set_brand_Novus : NID
NID_set_brand_Novus = MkNID 642

public export
NID_des_cdmf : NID
NID_des_cdmf = MkNID 643

public export
NID_rsaOAEPEncryptionSET : NID
NID_rsaOAEPEncryptionSET = MkNID 644

public export
NID_itu_t : NID
NID_itu_t = MkNID 645

public export
NID_joint_iso_itu_t : NID
NID_joint_iso_itu_t = MkNID 646

public export
NID_international_organizations : NID
NID_international_organizations = MkNID 647

public export
NID_ms_smartcard_login : NID
NID_ms_smartcard_login = MkNID 648

public export
NID_ms_upn : NID
NID_ms_upn = MkNID 649

public export
NID_aes_128_cfb1 : NID
NID_aes_128_cfb1 = MkNID 650

public export
NID_aes_192_cfb1 : NID
NID_aes_192_cfb1 = MkNID 651

public export
NID_aes_256_cfb1 : NID
NID_aes_256_cfb1 = MkNID 652

public export
NID_aes_128_cfb8 : NID
NID_aes_128_cfb8 = MkNID 653

public export
NID_aes_192_cfb8 : NID
NID_aes_192_cfb8 = MkNID 654

public export
NID_aes_256_cfb8 : NID
NID_aes_256_cfb8 = MkNID 655

public export
NID_des_cfb1 : NID
NID_des_cfb1 = MkNID 656

public export
NID_des_cfb8 : NID
NID_des_cfb8 = MkNID 657

public export
NID_des_ede3_cfb1 : NID
NID_des_ede3_cfb1 = MkNID 658

public export
NID_des_ede3_cfb8 : NID
NID_des_ede3_cfb8 = MkNID 659

public export
NID_streetAddress : NID
NID_streetAddress = MkNID 660

public export
NID_postalCode : NID
NID_postalCode = MkNID 661

public export
NID_id_ppl : NID
NID_id_ppl = MkNID 662

public export
NID_proxyCertInfo : NID
NID_proxyCertInfo = MkNID 663

public export
NID_id_ppl_anyLanguage : NID
NID_id_ppl_anyLanguage = MkNID 664

public export
NID_id_ppl_inheritAll : NID
NID_id_ppl_inheritAll = MkNID 665

public export
NID_name_constraints : NID
NID_name_constraints = MkNID 666

public export
NID_Independent : NID
NID_Independent = MkNID 667

public export
NID_sha256WithRSAEncryption : NID
NID_sha256WithRSAEncryption = MkNID 668

public export
NID_sha384WithRSAEncryption : NID
NID_sha384WithRSAEncryption = MkNID 669

public export
NID_sha512WithRSAEncryption : NID
NID_sha512WithRSAEncryption = MkNID 670

public export
NID_sha224WithRSAEncryption : NID
NID_sha224WithRSAEncryption = MkNID 671

public export
NID_sha256 : NID
NID_sha256 = MkNID 672

public export
NID_sha384 : NID
NID_sha384 = MkNID 673

public export
NID_sha512 : NID
NID_sha512 = MkNID 674

public export
NID_sha224 : NID
NID_sha224 = MkNID 675

public export
NID_identified_organization : NID
NID_identified_organization = MkNID 676

public export
NID_certicom_arc : NID
NID_certicom_arc = MkNID 677

public export
NID_wap : NID
NID_wap = MkNID 678

public export
NID_wap_wsg : NID
NID_wap_wsg = MkNID 679

public export
NID_X9_62_id_characteristic_two_basis : NID
NID_X9_62_id_characteristic_two_basis = MkNID 680

public export
NID_X9_62_onBasis : NID
NID_X9_62_onBasis = MkNID 681

public export
NID_X9_62_tpBasis : NID
NID_X9_62_tpBasis = MkNID 682

public export
NID_X9_62_ppBasis : NID
NID_X9_62_ppBasis = MkNID 683

public export
NID_X9_62_c2pnb163v1 : NID
NID_X9_62_c2pnb163v1 = MkNID 684

public export
NID_X9_62_c2pnb163v2 : NID
NID_X9_62_c2pnb163v2 = MkNID 685

public export
NID_X9_62_c2pnb163v3 : NID
NID_X9_62_c2pnb163v3 = MkNID 686

public export
NID_X9_62_c2pnb176v1 : NID
NID_X9_62_c2pnb176v1 = MkNID 687

public export
NID_X9_62_c2tnb191v1 : NID
NID_X9_62_c2tnb191v1 = MkNID 688

public export
NID_X9_62_c2tnb191v2 : NID
NID_X9_62_c2tnb191v2 = MkNID 689

public export
NID_X9_62_c2tnb191v3 : NID
NID_X9_62_c2tnb191v3 = MkNID 690

public export
NID_X9_62_c2onb191v4 : NID
NID_X9_62_c2onb191v4 = MkNID 691

public export
NID_X9_62_c2onb191v5 : NID
NID_X9_62_c2onb191v5 = MkNID 692

public export
NID_X9_62_c2pnb208w1 : NID
NID_X9_62_c2pnb208w1 = MkNID 693

public export
NID_X9_62_c2tnb239v1 : NID
NID_X9_62_c2tnb239v1 = MkNID 694

public export
NID_X9_62_c2tnb239v2 : NID
NID_X9_62_c2tnb239v2 = MkNID 695

public export
NID_X9_62_c2tnb239v3 : NID
NID_X9_62_c2tnb239v3 = MkNID 696

public export
NID_X9_62_c2onb239v4 : NID
NID_X9_62_c2onb239v4 = MkNID 697

public export
NID_X9_62_c2onb239v5 : NID
NID_X9_62_c2onb239v5 = MkNID 698

public export
NID_X9_62_c2pnb272w1 : NID
NID_X9_62_c2pnb272w1 = MkNID 699

public export
NID_X9_62_c2pnb304w1 : NID
NID_X9_62_c2pnb304w1 = MkNID 700

public export
NID_X9_62_c2tnb359v1 : NID
NID_X9_62_c2tnb359v1 = MkNID 701

public export
NID_X9_62_c2pnb368w1 : NID
NID_X9_62_c2pnb368w1 = MkNID 702

public export
NID_X9_62_c2tnb431r1 : NID
NID_X9_62_c2tnb431r1 = MkNID 703

public export
NID_secp112r1 : NID
NID_secp112r1 = MkNID 704

public export
NID_secp112r2 : NID
NID_secp112r2 = MkNID 705

public export
NID_secp128r1 : NID
NID_secp128r1 = MkNID 706

public export
NID_secp128r2 : NID
NID_secp128r2 = MkNID 707

public export
NID_secp160k1 : NID
NID_secp160k1 = MkNID 708

public export
NID_secp160r1 : NID
NID_secp160r1 = MkNID 709

public export
NID_secp160r2 : NID
NID_secp160r2 = MkNID 710

public export
NID_secp192k1 : NID
NID_secp192k1 = MkNID 711

public export
NID_secp224k1 : NID
NID_secp224k1 = MkNID 712

public export
NID_secp224r1 : NID
NID_secp224r1 = MkNID 713

public export
NID_secp256k1 : NID
NID_secp256k1 = MkNID 714

public export
NID_secp384r1 : NID
NID_secp384r1 = MkNID 715

public export
NID_secp521r1 : NID
NID_secp521r1 = MkNID 716

public export
NID_sect113r1 : NID
NID_sect113r1 = MkNID 717

public export
NID_sect113r2 : NID
NID_sect113r2 = MkNID 718

public export
NID_sect131r1 : NID
NID_sect131r1 = MkNID 719

public export
NID_sect131r2 : NID
NID_sect131r2 = MkNID 720

public export
NID_sect163k1 : NID
NID_sect163k1 = MkNID 721

public export
NID_sect163r1 : NID
NID_sect163r1 = MkNID 722

public export
NID_sect163r2 : NID
NID_sect163r2 = MkNID 723

public export
NID_sect193r1 : NID
NID_sect193r1 = MkNID 724

public export
NID_sect193r2 : NID
NID_sect193r2 = MkNID 725

public export
NID_sect233k1 : NID
NID_sect233k1 = MkNID 726

public export
NID_sect233r1 : NID
NID_sect233r1 = MkNID 727

public export
NID_sect239k1 : NID
NID_sect239k1 = MkNID 728

public export
NID_sect283k1 : NID
NID_sect283k1 = MkNID 729

public export
NID_sect283r1 : NID
NID_sect283r1 = MkNID 730

public export
NID_sect409k1 : NID
NID_sect409k1 = MkNID 731

public export
NID_sect409r1 : NID
NID_sect409r1 = MkNID 732

public export
NID_sect571k1 : NID
NID_sect571k1 = MkNID 733

public export
NID_sect571r1 : NID
NID_sect571r1 = MkNID 734

public export
NID_wap_wsg_idm_ecid_wtls1 : NID
NID_wap_wsg_idm_ecid_wtls1 = MkNID 735

public export
NID_wap_wsg_idm_ecid_wtls3 : NID
NID_wap_wsg_idm_ecid_wtls3 = MkNID 736

public export
NID_wap_wsg_idm_ecid_wtls4 : NID
NID_wap_wsg_idm_ecid_wtls4 = MkNID 737

public export
NID_wap_wsg_idm_ecid_wtls5 : NID
NID_wap_wsg_idm_ecid_wtls5 = MkNID 738

public export
NID_wap_wsg_idm_ecid_wtls6 : NID
NID_wap_wsg_idm_ecid_wtls6 = MkNID 739

public export
NID_wap_wsg_idm_ecid_wtls7 : NID
NID_wap_wsg_idm_ecid_wtls7 = MkNID 740

public export
NID_wap_wsg_idm_ecid_wtls8 : NID
NID_wap_wsg_idm_ecid_wtls8 = MkNID 741

public export
NID_wap_wsg_idm_ecid_wtls9 : NID
NID_wap_wsg_idm_ecid_wtls9 = MkNID 742

public export
NID_wap_wsg_idm_ecid_wtls10 : NID
NID_wap_wsg_idm_ecid_wtls10 = MkNID 743

public export
NID_wap_wsg_idm_ecid_wtls11 : NID
NID_wap_wsg_idm_ecid_wtls11 = MkNID 744

public export
NID_wap_wsg_idm_ecid_wtls12 : NID
NID_wap_wsg_idm_ecid_wtls12 = MkNID 745

public export
NID_any_policy : NID
NID_any_policy = MkNID 746

public export
NID_policy_mappings : NID
NID_policy_mappings = MkNID 747

public export
NID_inhibit_any_policy : NID
NID_inhibit_any_policy = MkNID 748

public export
NID_ipsec3 : NID
NID_ipsec3 = MkNID 749

public export
NID_ipsec4 : NID
NID_ipsec4 = MkNID 750

public export
NID_camellia_128_cbc : NID
NID_camellia_128_cbc = MkNID 751

public export
NID_camellia_192_cbc : NID
NID_camellia_192_cbc = MkNID 752

public export
NID_camellia_256_cbc : NID
NID_camellia_256_cbc = MkNID 753

public export
NID_camellia_128_ecb : NID
NID_camellia_128_ecb = MkNID 754

public export
NID_camellia_192_ecb : NID
NID_camellia_192_ecb = MkNID 755

public export
NID_camellia_256_ecb : NID
NID_camellia_256_ecb = MkNID 756

public export
NID_camellia_128_cfb128 : NID
NID_camellia_128_cfb128 = MkNID 757

public export
NID_camellia_192_cfb128 : NID
NID_camellia_192_cfb128 = MkNID 758

public export
NID_camellia_256_cfb128 : NID
NID_camellia_256_cfb128 = MkNID 759

public export
NID_camellia_128_cfb1 : NID
NID_camellia_128_cfb1 = MkNID 760

public export
NID_camellia_192_cfb1 : NID
NID_camellia_192_cfb1 = MkNID 761

public export
NID_camellia_256_cfb1 : NID
NID_camellia_256_cfb1 = MkNID 762

public export
NID_camellia_128_cfb8 : NID
NID_camellia_128_cfb8 = MkNID 763

public export
NID_camellia_192_cfb8 : NID
NID_camellia_192_cfb8 = MkNID 764

public export
NID_camellia_256_cfb8 : NID
NID_camellia_256_cfb8 = MkNID 765

public export
NID_camellia_128_ofb128 : NID
NID_camellia_128_ofb128 = MkNID 766

public export
NID_camellia_192_ofb128 : NID
NID_camellia_192_ofb128 = MkNID 767

public export
NID_camellia_256_ofb128 : NID
NID_camellia_256_ofb128 = MkNID 768

public export
NID_subject_directory_attributes : NID
NID_subject_directory_attributes = MkNID 769

public export
NID_issuing_distribution_point : NID
NID_issuing_distribution_point = MkNID 770

public export
NID_certificate_issuer : NID
NID_certificate_issuer = MkNID 771

public export
NID_korea : NID
NID_korea = MkNID 772

public export
NID_kisa : NID
NID_kisa = MkNID 773

public export
NID_kftc : NID
NID_kftc = MkNID 774

public export
NID_npki_alg : NID
NID_npki_alg = MkNID 775

public export
NID_seed_ecb : NID
NID_seed_ecb = MkNID 776

public export
NID_seed_cbc : NID
NID_seed_cbc = MkNID 777

public export
NID_seed_ofb128 : NID
NID_seed_ofb128 = MkNID 778

public export
NID_seed_cfb128 : NID
NID_seed_cfb128 = MkNID 779

public export
NID_hmac_md5 : NID
NID_hmac_md5 = MkNID 780

public export
NID_hmac_sha1 : NID
NID_hmac_sha1 = MkNID 781

public export
NID_id_PasswordBasedMAC : NID
NID_id_PasswordBasedMAC = MkNID 782

public export
NID_id_DHBasedMac : NID
NID_id_DHBasedMac = MkNID 783

public export
NID_id_it_suppLangTags : NID
NID_id_it_suppLangTags = MkNID 784

public export
NID_caRepository : NID
NID_caRepository = MkNID 785

public export
NID_id_smime_ct_compressedData : NID
NID_id_smime_ct_compressedData = MkNID 786

public export
NID_id_ct_asciiTextWithCRLF : NID
NID_id_ct_asciiTextWithCRLF = MkNID 787

public export
NID_id_aes128_wrap : NID
NID_id_aes128_wrap = MkNID 788

public export
NID_id_aes192_wrap : NID
NID_id_aes192_wrap = MkNID 789

public export
NID_id_aes256_wrap : NID
NID_id_aes256_wrap = MkNID 790

public export
NID_ecdsa_with_Recommended : NID
NID_ecdsa_with_Recommended = MkNID 791

public export
NID_ecdsa_with_Specified : NID
NID_ecdsa_with_Specified = MkNID 792

public export
NID_ecdsa_with_SHA224 : NID
NID_ecdsa_with_SHA224 = MkNID 793

public export
NID_ecdsa_with_SHA256 : NID
NID_ecdsa_with_SHA256 = MkNID 794

public export
NID_ecdsa_with_SHA384 : NID
NID_ecdsa_with_SHA384 = MkNID 795

public export
NID_ecdsa_with_SHA512 : NID
NID_ecdsa_with_SHA512 = MkNID 796

public export
NID_hmacWithMD5 : NID
NID_hmacWithMD5 = MkNID 797

public export
NID_hmacWithSHA224 : NID
NID_hmacWithSHA224 = MkNID 798

public export
NID_hmacWithSHA256 : NID
NID_hmacWithSHA256 = MkNID 799

public export
NID_hmacWithSHA384 : NID
NID_hmacWithSHA384 = MkNID 800

public export
NID_hmacWithSHA512 : NID
NID_hmacWithSHA512 = MkNID 801

public export
NID_dsa_with_SHA224 : NID
NID_dsa_with_SHA224 = MkNID 802

public export
NID_dsa_with_SHA256 : NID
NID_dsa_with_SHA256 = MkNID 803

public export
NID_whirlpool : NID
NID_whirlpool = MkNID 804

public export
NID_cryptopro : NID
NID_cryptopro = MkNID 805

public export
NID_cryptocom : NID
NID_cryptocom = MkNID 806

public export
NID_id_GostR3411_94_with_GostR3410_2001 : NID
NID_id_GostR3411_94_with_GostR3410_2001 = MkNID 807

public export
NID_id_GostR3411_94_with_GostR3410_94 : NID
NID_id_GostR3411_94_with_GostR3410_94 = MkNID 808

public export
NID_id_GostR3411_94 : NID
NID_id_GostR3411_94 = MkNID 809

public export
NID_id_HMACGostR3411_94 : NID
NID_id_HMACGostR3411_94 = MkNID 810

public export
NID_id_GostR3410_2001 : NID
NID_id_GostR3410_2001 = MkNID 811

public export
NID_id_GostR3410_94 : NID
NID_id_GostR3410_94 = MkNID 812

public export
NID_id_Gost28147_89 : NID
NID_id_Gost28147_89 = MkNID 813

public export
NID_gost89_cnt : NID
NID_gost89_cnt = MkNID 814

public export
NID_id_Gost28147_89_MAC : NID
NID_id_Gost28147_89_MAC = MkNID 815

public export
NID_id_GostR3411_94_prf : NID
NID_id_GostR3411_94_prf = MkNID 816

public export
NID_id_GostR3410_2001DH : NID
NID_id_GostR3410_2001DH = MkNID 817

public export
NID_id_GostR3410_94DH : NID
NID_id_GostR3410_94DH = MkNID 818

public export
NID_id_Gost28147_89_CryptoPro_KeyMeshing : NID
NID_id_Gost28147_89_CryptoPro_KeyMeshing = MkNID 819

public export
NID_id_Gost28147_89_None_KeyMeshing : NID
NID_id_Gost28147_89_None_KeyMeshing = MkNID 820

public export
NID_id_GostR3411_94_TestParamSet : NID
NID_id_GostR3411_94_TestParamSet = MkNID 821

public export
NID_id_GostR3411_94_CryptoProParamSet : NID
NID_id_GostR3411_94_CryptoProParamSet = MkNID 822

public export
NID_id_Gost28147_89_TestParamSet : NID
NID_id_Gost28147_89_TestParamSet = MkNID 823

public export
NID_id_Gost28147_89_CryptoPro_A_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_A_ParamSet = MkNID 824

public export
NID_id_Gost28147_89_CryptoPro_B_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_B_ParamSet = MkNID 825

public export
NID_id_Gost28147_89_CryptoPro_C_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_C_ParamSet = MkNID 826

public export
NID_id_Gost28147_89_CryptoPro_D_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_D_ParamSet = MkNID 827

public export
NID_id_Gost28147_89_CryptoPro_Oscar_1_1_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_Oscar_1_1_ParamSet = MkNID 828

public export
NID_id_Gost28147_89_CryptoPro_Oscar_1_0_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_Oscar_1_0_ParamSet = MkNID 829

public export
NID_id_Gost28147_89_CryptoPro_RIC_1_ParamSet : NID
NID_id_Gost28147_89_CryptoPro_RIC_1_ParamSet = MkNID 830

public export
NID_id_GostR3410_94_TestParamSet : NID
NID_id_GostR3410_94_TestParamSet = MkNID 831

public export
NID_id_GostR3410_94_CryptoPro_A_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_A_ParamSet = MkNID 832

public export
NID_id_GostR3410_94_CryptoPro_B_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_B_ParamSet = MkNID 833

public export
NID_id_GostR3410_94_CryptoPro_C_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_C_ParamSet = MkNID 834

public export
NID_id_GostR3410_94_CryptoPro_D_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_D_ParamSet = MkNID 835

public export
NID_id_GostR3410_94_CryptoPro_XchA_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_XchA_ParamSet = MkNID 836

public export
NID_id_GostR3410_94_CryptoPro_XchB_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_XchB_ParamSet = MkNID 837

public export
NID_id_GostR3410_94_CryptoPro_XchC_ParamSet : NID
NID_id_GostR3410_94_CryptoPro_XchC_ParamSet = MkNID 838

public export
NID_id_GostR3410_2001_TestParamSet : NID
NID_id_GostR3410_2001_TestParamSet = MkNID 839

public export
NID_id_GostR3410_2001_CryptoPro_A_ParamSet : NID
NID_id_GostR3410_2001_CryptoPro_A_ParamSet = MkNID 840

public export
NID_id_GostR3410_2001_CryptoPro_B_ParamSet : NID
NID_id_GostR3410_2001_CryptoPro_B_ParamSet = MkNID 841

public export
NID_id_GostR3410_2001_CryptoPro_C_ParamSet : NID
NID_id_GostR3410_2001_CryptoPro_C_ParamSet = MkNID 842

public export
NID_id_GostR3410_2001_CryptoPro_XchA_ParamSet : NID
NID_id_GostR3410_2001_CryptoPro_XchA_ParamSet = MkNID 843

public export
NID_id_GostR3410_2001_CryptoPro_XchB_ParamSet : NID
NID_id_GostR3410_2001_CryptoPro_XchB_ParamSet = MkNID 844

public export
NID_id_GostR3410_94_a : NID
NID_id_GostR3410_94_a = MkNID 845

public export
NID_id_GostR3410_94_aBis : NID
NID_id_GostR3410_94_aBis = MkNID 846

public export
NID_id_GostR3410_94_b : NID
NID_id_GostR3410_94_b = MkNID 847

public export
NID_id_GostR3410_94_bBis : NID
NID_id_GostR3410_94_bBis = MkNID 848

public export
NID_id_Gost28147_89_cc : NID
NID_id_Gost28147_89_cc = MkNID 849

public export
NID_id_GostR3410_94_cc : NID
NID_id_GostR3410_94_cc = MkNID 850

public export
NID_id_GostR3410_2001_cc : NID
NID_id_GostR3410_2001_cc = MkNID 851

public export
NID_id_GostR3411_94_with_GostR3410_94_cc : NID
NID_id_GostR3411_94_with_GostR3410_94_cc = MkNID 852

public export
NID_id_GostR3411_94_with_GostR3410_2001_cc : NID
NID_id_GostR3411_94_with_GostR3410_2001_cc = MkNID 853

public export
NID_id_GostR3410_2001_ParamSet_cc : NID
NID_id_GostR3410_2001_ParamSet_cc = MkNID 854

public export
NID_hmac : NID
NID_hmac = MkNID 855

public export
NID_LocalKeySet : NID
NID_LocalKeySet = MkNID 856

public export
NID_freshest_crl : NID
NID_freshest_crl = MkNID 857

public export
NID_id_on_permanentIdentifier : NID
NID_id_on_permanentIdentifier = MkNID 858

public export
NID_searchGuide : NID
NID_searchGuide = MkNID 859

public export
NID_businessCategory : NID
NID_businessCategory = MkNID 860

public export
NID_postalAddress : NID
NID_postalAddress = MkNID 861

public export
NID_postOfficeBox : NID
NID_postOfficeBox = MkNID 862

public export
NID_physicalDeliveryOfficeName : NID
NID_physicalDeliveryOfficeName = MkNID 863

public export
NID_telephoneNumber : NID
NID_telephoneNumber = MkNID 864

public export
NID_telexNumber : NID
NID_telexNumber = MkNID 865

public export
NID_teletexTerminalIdentifier : NID
NID_teletexTerminalIdentifier = MkNID 866

public export
NID_facsimileTelephoneNumber : NID
NID_facsimileTelephoneNumber = MkNID 867

public export
NID_x121Address : NID
NID_x121Address = MkNID 868

public export
NID_internationaliSDNNumber : NID
NID_internationaliSDNNumber = MkNID 869

public export
NID_registeredAddress : NID
NID_registeredAddress = MkNID 870

public export
NID_destinationIndicator : NID
NID_destinationIndicator = MkNID 871

public export
NID_preferredDeliveryMethod : NID
NID_preferredDeliveryMethod = MkNID 872

public export
NID_presentationAddress : NID
NID_presentationAddress = MkNID 873

public export
NID_supportedApplicationContext : NID
NID_supportedApplicationContext = MkNID 874

public export
NID_member : NID
NID_member = MkNID 875

public export
NID_owner : NID
NID_owner = MkNID 876

public export
NID_roleOccupant : NID
NID_roleOccupant = MkNID 877

public export
NID_seeAlso : NID
NID_seeAlso = MkNID 878

public export
NID_userPassword : NID
NID_userPassword = MkNID 879

public export
NID_userCertificate : NID
NID_userCertificate = MkNID 880

public export
NID_cACertificate : NID
NID_cACertificate = MkNID 881

public export
NID_authorityRevocationList : NID
NID_authorityRevocationList = MkNID 882

public export
NID_certificateRevocationList : NID
NID_certificateRevocationList = MkNID 883

public export
NID_crossCertificatePair : NID
NID_crossCertificatePair = MkNID 884

public export
NID_enhancedSearchGuide : NID
NID_enhancedSearchGuide = MkNID 885

public export
NID_protocolInformation : NID
NID_protocolInformation = MkNID 886

public export
NID_distinguishedName : NID
NID_distinguishedName = MkNID 887

public export
NID_uniqueMember : NID
NID_uniqueMember = MkNID 888

public export
NID_houseIdentifier : NID
NID_houseIdentifier = MkNID 889

public export
NID_supportedAlgorithms : NID
NID_supportedAlgorithms = MkNID 890

public export
NID_deltaRevocationList : NID
NID_deltaRevocationList = MkNID 891

public export
NID_dmdName : NID
NID_dmdName = MkNID 892

public export
NID_id_alg_PWRI_KEK : NID
NID_id_alg_PWRI_KEK = MkNID 893

public export
NID_cmac : NID
NID_cmac = MkNID 894

public export
NID_aes_128_gcm : NID
NID_aes_128_gcm = MkNID 895

public export
NID_aes_128_ccm : NID
NID_aes_128_ccm = MkNID 896

public export
NID_id_aes128_wrap_pad : NID
NID_id_aes128_wrap_pad = MkNID 897

public export
NID_aes_192_gcm : NID
NID_aes_192_gcm = MkNID 898

public export
NID_aes_192_ccm : NID
NID_aes_192_ccm = MkNID 899

public export
NID_id_aes192_wrap_pad : NID
NID_id_aes192_wrap_pad = MkNID 900

public export
NID_aes_256_gcm : NID
NID_aes_256_gcm = MkNID 901

public export
NID_aes_256_ccm : NID
NID_aes_256_ccm = MkNID 902

public export
NID_id_aes256_wrap_pad : NID
NID_id_aes256_wrap_pad = MkNID 903

public export
NID_aes_128_ctr : NID
NID_aes_128_ctr = MkNID 904

public export
NID_aes_192_ctr : NID
NID_aes_192_ctr = MkNID 905

public export
NID_aes_256_ctr : NID
NID_aes_256_ctr = MkNID 906

public export
NID_id_camellia128_wrap : NID
NID_id_camellia128_wrap = MkNID 907

public export
NID_id_camellia192_wrap : NID
NID_id_camellia192_wrap = MkNID 908

public export
NID_id_camellia256_wrap : NID
NID_id_camellia256_wrap = MkNID 909

public export
NID_anyExtendedKeyUsage : NID
NID_anyExtendedKeyUsage = MkNID 910

public export
NID_mgf1 : NID
NID_mgf1 = MkNID 911

public export
NID_rsassaPss : NID
NID_rsassaPss = MkNID 912

public export
NID_aes_128_xts : NID
NID_aes_128_xts = MkNID 913

public export
NID_aes_256_xts : NID
NID_aes_256_xts = MkNID 914

public export
NID_rc4_hmac_md5 : NID
NID_rc4_hmac_md5 = MkNID 915

public export
NID_aes_128_cbc_hmac_sha1 : NID
NID_aes_128_cbc_hmac_sha1 = MkNID 916

public export
NID_aes_192_cbc_hmac_sha1 : NID
NID_aes_192_cbc_hmac_sha1 = MkNID 917

public export
NID_aes_256_cbc_hmac_sha1 : NID
NID_aes_256_cbc_hmac_sha1 = MkNID 918

public export
NID_rsaesOaep : NID
NID_rsaesOaep = MkNID 919

public export
NID_dhpublicnumber : NID
NID_dhpublicnumber = MkNID 920

public export
NID_brainpoolP160r1 : NID
NID_brainpoolP160r1 = MkNID 921

public export
NID_brainpoolP160t1 : NID
NID_brainpoolP160t1 = MkNID 922

public export
NID_brainpoolP192r1 : NID
NID_brainpoolP192r1 = MkNID 923

public export
NID_brainpoolP192t1 : NID
NID_brainpoolP192t1 = MkNID 924

public export
NID_brainpoolP224r1 : NID
NID_brainpoolP224r1 = MkNID 925

public export
NID_brainpoolP224t1 : NID
NID_brainpoolP224t1 = MkNID 926

public export
NID_brainpoolP256r1 : NID
NID_brainpoolP256r1 = MkNID 927

public export
NID_brainpoolP256t1 : NID
NID_brainpoolP256t1 = MkNID 928

public export
NID_brainpoolP320r1 : NID
NID_brainpoolP320r1 = MkNID 929

public export
NID_brainpoolP320t1 : NID
NID_brainpoolP320t1 = MkNID 930

public export
NID_brainpoolP384r1 : NID
NID_brainpoolP384r1 = MkNID 931

public export
NID_brainpoolP384t1 : NID
NID_brainpoolP384t1 = MkNID 932

public export
NID_brainpoolP512r1 : NID
NID_brainpoolP512r1 = MkNID 933

public export
NID_brainpoolP512t1 : NID
NID_brainpoolP512t1 = MkNID 934

public export
NID_pSpecified : NID
NID_pSpecified = MkNID 935

public export
NID_dhSinglePass_stdDH_sha1kdf_scheme : NID
NID_dhSinglePass_stdDH_sha1kdf_scheme = MkNID 936

public export
NID_dhSinglePass_stdDH_sha224kdf_scheme : NID
NID_dhSinglePass_stdDH_sha224kdf_scheme = MkNID 937

public export
NID_dhSinglePass_stdDH_sha256kdf_scheme : NID
NID_dhSinglePass_stdDH_sha256kdf_scheme = MkNID 938

public export
NID_dhSinglePass_stdDH_sha384kdf_scheme : NID
NID_dhSinglePass_stdDH_sha384kdf_scheme = MkNID 939

public export
NID_dhSinglePass_stdDH_sha512kdf_scheme : NID
NID_dhSinglePass_stdDH_sha512kdf_scheme = MkNID 940

public export
NID_dhSinglePass_cofactorDH_sha1kdf_scheme : NID
NID_dhSinglePass_cofactorDH_sha1kdf_scheme = MkNID 941

public export
NID_dhSinglePass_cofactorDH_sha224kdf_scheme : NID
NID_dhSinglePass_cofactorDH_sha224kdf_scheme = MkNID 942

public export
NID_dhSinglePass_cofactorDH_sha256kdf_scheme : NID
NID_dhSinglePass_cofactorDH_sha256kdf_scheme = MkNID 943

public export
NID_dhSinglePass_cofactorDH_sha384kdf_scheme : NID
NID_dhSinglePass_cofactorDH_sha384kdf_scheme = MkNID 944

public export
NID_dhSinglePass_cofactorDH_sha512kdf_scheme : NID
NID_dhSinglePass_cofactorDH_sha512kdf_scheme = MkNID 945

public export
NID_dh_std_kdf : NID
NID_dh_std_kdf = MkNID 946

public export
NID_dh_cofactor_kdf : NID
NID_dh_cofactor_kdf = MkNID 947

public export
NID_aes_128_cbc_hmac_sha256 : NID
NID_aes_128_cbc_hmac_sha256 = MkNID 948

public export
NID_aes_192_cbc_hmac_sha256 : NID
NID_aes_192_cbc_hmac_sha256 = MkNID 949

public export
NID_aes_256_cbc_hmac_sha256 : NID
NID_aes_256_cbc_hmac_sha256 = MkNID 950

public export
NID_ct_precert_scts : NID
NID_ct_precert_scts = MkNID 951

public export
NID_ct_precert_poison : NID
NID_ct_precert_poison = MkNID 952

public export
NID_ct_precert_signer : NID
NID_ct_precert_signer = MkNID 953

public export
NID_ct_cert_scts : NID
NID_ct_cert_scts = MkNID 954

public export
NID_jurisdictionLocalityName : NID
NID_jurisdictionLocalityName = MkNID 955

public export
NID_jurisdictionStateOrProvinceName : NID
NID_jurisdictionStateOrProvinceName = MkNID 956

public export
NID_jurisdictionCountryName : NID
NID_jurisdictionCountryName = MkNID 957

public export
NID_aes_128_ocb : NID
NID_aes_128_ocb = MkNID 958

public export
NID_aes_192_ocb : NID
NID_aes_192_ocb = MkNID 959

public export
NID_aes_256_ocb : NID
NID_aes_256_ocb = MkNID 960

public export
NID_camellia_128_gcm : NID
NID_camellia_128_gcm = MkNID 961

public export
NID_camellia_128_ccm : NID
NID_camellia_128_ccm = MkNID 962

public export
NID_camellia_128_ctr : NID
NID_camellia_128_ctr = MkNID 963

public export
NID_camellia_128_cmac : NID
NID_camellia_128_cmac = MkNID 964

public export
NID_camellia_192_gcm : NID
NID_camellia_192_gcm = MkNID 965

public export
NID_camellia_192_ccm : NID
NID_camellia_192_ccm = MkNID 966

public export
NID_camellia_192_ctr : NID
NID_camellia_192_ctr = MkNID 967

public export
NID_camellia_192_cmac : NID
NID_camellia_192_cmac = MkNID 968

public export
NID_camellia_256_gcm : NID
NID_camellia_256_gcm = MkNID 969

public export
NID_camellia_256_ccm : NID
NID_camellia_256_ccm = MkNID 970

public export
NID_camellia_256_ctr : NID
NID_camellia_256_ctr = MkNID 971

public export
NID_camellia_256_cmac : NID
NID_camellia_256_cmac = MkNID 972

public export
NID_id_scrypt : NID
NID_id_scrypt = MkNID 973

public export
NID_id_tc26 : NID
NID_id_tc26 = MkNID 974

public export
NID_gost89_cnt_12 : NID
NID_gost89_cnt_12 = MkNID 975

public export
NID_gost_mac_12 : NID
NID_gost_mac_12 = MkNID 976

public export
NID_id_tc26_algorithms : NID
NID_id_tc26_algorithms = MkNID 977

public export
NID_id_tc26_sign : NID
NID_id_tc26_sign = MkNID 978

public export
NID_id_GostR3410_2012_256 : NID
NID_id_GostR3410_2012_256 = MkNID 979

public export
NID_id_GostR3410_2012_512 : NID
NID_id_GostR3410_2012_512 = MkNID 980

public export
NID_id_tc26_digest : NID
NID_id_tc26_digest = MkNID 981

public export
NID_id_GostR3411_2012_256 : NID
NID_id_GostR3411_2012_256 = MkNID 982

public export
NID_id_GostR3411_2012_512 : NID
NID_id_GostR3411_2012_512 = MkNID 983

public export
NID_id_tc26_signwithdigest : NID
NID_id_tc26_signwithdigest = MkNID 984

public export
NID_id_tc26_signwithdigest_gost3410_2012_256 : NID
NID_id_tc26_signwithdigest_gost3410_2012_256 = MkNID 985

public export
NID_id_tc26_signwithdigest_gost3410_2012_512 : NID
NID_id_tc26_signwithdigest_gost3410_2012_512 = MkNID 986

public export
NID_id_tc26_mac : NID
NID_id_tc26_mac = MkNID 987

public export
NID_id_tc26_hmac_gost_3411_2012_256 : NID
NID_id_tc26_hmac_gost_3411_2012_256 = MkNID 988

public export
NID_id_tc26_hmac_gost_3411_2012_512 : NID
NID_id_tc26_hmac_gost_3411_2012_512 = MkNID 989

public export
NID_id_tc26_cipher : NID
NID_id_tc26_cipher = MkNID 990

public export
NID_id_tc26_agreement : NID
NID_id_tc26_agreement = MkNID 991

public export
NID_id_tc26_agreement_gost_3410_2012_256 : NID
NID_id_tc26_agreement_gost_3410_2012_256 = MkNID 992

public export
NID_id_tc26_agreement_gost_3410_2012_512 : NID
NID_id_tc26_agreement_gost_3410_2012_512 = MkNID 993

public export
NID_id_tc26_constants : NID
NID_id_tc26_constants = MkNID 994

public export
NID_id_tc26_sign_constants : NID
NID_id_tc26_sign_constants = MkNID 995

public export
NID_id_tc26_gost_3410_2012_512_constants : NID
NID_id_tc26_gost_3410_2012_512_constants = MkNID 996

public export
NID_id_tc26_gost_3410_2012_512_paramSetTest : NID
NID_id_tc26_gost_3410_2012_512_paramSetTest = MkNID 997

public export
NID_id_tc26_gost_3410_2012_512_paramSetA : NID
NID_id_tc26_gost_3410_2012_512_paramSetA = MkNID 998

public export
NID_id_tc26_gost_3410_2012_512_paramSetB : NID
NID_id_tc26_gost_3410_2012_512_paramSetB = MkNID 999

public export
NID_id_tc26_digest_constants : NID
NID_id_tc26_digest_constants = MkNID 1000

public export
NID_id_tc26_cipher_constants : NID
NID_id_tc26_cipher_constants = MkNID 1001

public export
NID_id_tc26_gost_28147_constants : NID
NID_id_tc26_gost_28147_constants = MkNID 1002

public export
NID_id_tc26_gost_28147_param_Z : NID
NID_id_tc26_gost_28147_param_Z = MkNID 1003

public export
NID_INN : NID
NID_INN = MkNID 1004

public export
NID_OGRN : NID
NID_OGRN = MkNID 1005

public export
NID_SNILS : NID
NID_SNILS = MkNID 1006

public export
NID_subjectSignTool : NID
NID_subjectSignTool = MkNID 1007

public export
NID_issuerSignTool : NID
NID_issuerSignTool = MkNID 1008

public export
NID_gost89_cbc : NID
NID_gost89_cbc = MkNID 1009

public export
NID_gost89_ecb : NID
NID_gost89_ecb = MkNID 1010

public export
NID_gost89_ctr : NID
NID_gost89_ctr = MkNID 1011

public export
NID_kuznyechik_ecb : NID
NID_kuznyechik_ecb = MkNID 1012

public export
NID_kuznyechik_ctr : NID
NID_kuznyechik_ctr = MkNID 1013

public export
NID_kuznyechik_ofb : NID
NID_kuznyechik_ofb = MkNID 1014

public export
NID_kuznyechik_cbc : NID
NID_kuznyechik_cbc = MkNID 1015

public export
NID_kuznyechik_cfb : NID
NID_kuznyechik_cfb = MkNID 1016

public export
NID_kuznyechik_mac : NID
NID_kuznyechik_mac = MkNID 1017

public export
NID_chacha20_poly1305 : NID
NID_chacha20_poly1305 = MkNID 1018

public export
NID_chacha20 : NID
NID_chacha20 = MkNID 1019

public export
NID_tlsfeature : NID
NID_tlsfeature = MkNID 1020

public export
NID_tls1_prf : NID
NID_tls1_prf = MkNID 1021

public export
NID_ipsec_IKE : NID
NID_ipsec_IKE = MkNID 1022

public export
NID_capwapAC : NID
NID_capwapAC = MkNID 1023

public export
NID_capwapWTP : NID
NID_capwapWTP = MkNID 1024

public export
NID_sshClient : NID
NID_sshClient = MkNID 1025

public export
NID_sshServer : NID
NID_sshServer = MkNID 1026

public export
NID_sendRouter : NID
NID_sendRouter = MkNID 1027

public export
NID_sendProxiedRouter : NID
NID_sendProxiedRouter = MkNID 1028

public export
NID_sendOwner : NID
NID_sendOwner = MkNID 1029

public export
NID_sendProxiedOwner : NID
NID_sendProxiedOwner = MkNID 1030

public export
NID_id_pkinit : NID
NID_id_pkinit = MkNID 1031

public export
NID_pkInitClientAuth : NID
NID_pkInitClientAuth = MkNID 1032

public export
NID_pkInitKDC : NID
NID_pkInitKDC = MkNID 1033

public export
NID_X25519 : NID
NID_X25519 = MkNID 1034

public export
NID_X448 : NID
NID_X448 = MkNID 1035

public export
NID_hkdf : NID
NID_hkdf = MkNID 1036

public export
NID_kx_rsa : NID
NID_kx_rsa = MkNID 1037

public export
NID_kx_ecdhe : NID
NID_kx_ecdhe = MkNID 1038

public export
NID_kx_dhe : NID
NID_kx_dhe = MkNID 1039

public export
NID_kx_ecdhe_psk : NID
NID_kx_ecdhe_psk = MkNID 1040

public export
NID_kx_dhe_psk : NID
NID_kx_dhe_psk = MkNID 1041

public export
NID_kx_rsa_psk : NID
NID_kx_rsa_psk = MkNID 1042

public export
NID_kx_psk : NID
NID_kx_psk = MkNID 1043

public export
NID_kx_srp : NID
NID_kx_srp = MkNID 1044

public export
NID_kx_gost : NID
NID_kx_gost = MkNID 1045

public export
NID_auth_rsa : NID
NID_auth_rsa = MkNID 1046

public export
NID_auth_ecdsa : NID
NID_auth_ecdsa = MkNID 1047

public export
NID_auth_psk : NID
NID_auth_psk = MkNID 1048

public export
NID_auth_dss : NID
NID_auth_dss = MkNID 1049

public export
NID_auth_gost01 : NID
NID_auth_gost01 = MkNID 1050

public export
NID_auth_gost12 : NID
NID_auth_gost12 = MkNID 1051

public export
NID_auth_srp : NID
NID_auth_srp = MkNID 1052

public export
NID_auth_null : NID
NID_auth_null = MkNID 1053

public export
NID_fips_none : NID
NID_fips_none = MkNID 1054

public export
NID_fips_140_2 : NID
NID_fips_140_2 = MkNID 1055

public export
NID_blake2b512 : NID
NID_blake2b512 = MkNID 1056

public export
NID_blake2s256 : NID
NID_blake2s256 = MkNID 1057

public export
NID_id_smime_ct_contentCollection : NID
NID_id_smime_ct_contentCollection = MkNID 1058

public export
NID_id_smime_ct_authEnvelopedData : NID
NID_id_smime_ct_authEnvelopedData = MkNID 1059

public export
NID_id_ct_xml : NID
NID_id_ct_xml = MkNID 1060

public export
NID_poly1305 : NID
NID_poly1305 = MkNID 1061

public export
NID_siphash : NID
NID_siphash = MkNID 1062

public export
NID_kx_any : NID
NID_kx_any = MkNID 1063

public export
NID_auth_any : NID
NID_auth_any = MkNID 1064

public export
NID_aria_128_ecb : NID
NID_aria_128_ecb = MkNID 1065

public export
NID_aria_128_cbc : NID
NID_aria_128_cbc = MkNID 1066

public export
NID_aria_128_cfb128 : NID
NID_aria_128_cfb128 = MkNID 1067

public export
NID_aria_128_ofb128 : NID
NID_aria_128_ofb128 = MkNID 1068

public export
NID_aria_128_ctr : NID
NID_aria_128_ctr = MkNID 1069

public export
NID_aria_192_ecb : NID
NID_aria_192_ecb = MkNID 1070

public export
NID_aria_192_cbc : NID
NID_aria_192_cbc = MkNID 1071

public export
NID_aria_192_cfb128 : NID
NID_aria_192_cfb128 = MkNID 1072

public export
NID_aria_192_ofb128 : NID
NID_aria_192_ofb128 = MkNID 1073

public export
NID_aria_192_ctr : NID
NID_aria_192_ctr = MkNID 1074

public export
NID_aria_256_ecb : NID
NID_aria_256_ecb = MkNID 1075

public export
NID_aria_256_cbc : NID
NID_aria_256_cbc = MkNID 1076

public export
NID_aria_256_cfb128 : NID
NID_aria_256_cfb128 = MkNID 1077

public export
NID_aria_256_ofb128 : NID
NID_aria_256_ofb128 = MkNID 1078

public export
NID_aria_256_ctr : NID
NID_aria_256_ctr = MkNID 1079

public export
NID_aria_128_cfb1 : NID
NID_aria_128_cfb1 = MkNID 1080

public export
NID_aria_192_cfb1 : NID
NID_aria_192_cfb1 = MkNID 1081

public export
NID_aria_256_cfb1 : NID
NID_aria_256_cfb1 = MkNID 1082

public export
NID_aria_128_cfb8 : NID
NID_aria_128_cfb8 = MkNID 1083

public export
NID_aria_192_cfb8 : NID
NID_aria_192_cfb8 = MkNID 1084

public export
NID_aria_256_cfb8 : NID
NID_aria_256_cfb8 = MkNID 1085

public export
NID_id_smime_aa_signingCertificateV2 : NID
NID_id_smime_aa_signingCertificateV2 = MkNID 1086

public export
NID_ED25519 : NID
NID_ED25519 = MkNID 1087

public export
NID_ED448 : NID
NID_ED448 = MkNID 1088

public export
NID_organizationIdentifier : NID
NID_organizationIdentifier = MkNID 1089

public export
NID_countryCode3c : NID
NID_countryCode3c = MkNID 1090

public export
NID_countryCode3n : NID
NID_countryCode3n = MkNID 1091

public export
NID_dnsName : NID
NID_dnsName = MkNID 1092

public export
NID_x509ExtAdmission : NID
NID_x509ExtAdmission = MkNID 1093

public export
NID_sha512_224 : NID
NID_sha512_224 = MkNID 1094

public export
NID_sha512_256 : NID
NID_sha512_256 = MkNID 1095

public export
NID_sha3_224 : NID
NID_sha3_224 = MkNID 1096

public export
NID_sha3_256 : NID
NID_sha3_256 = MkNID 1097

public export
NID_sha3_384 : NID
NID_sha3_384 = MkNID 1098

public export
NID_sha3_512 : NID
NID_sha3_512 = MkNID 1099

public export
NID_shake128 : NID
NID_shake128 = MkNID 1100

public export
NID_shake256 : NID
NID_shake256 = MkNID 1101

public export
NID_hmac_sha3_224 : NID
NID_hmac_sha3_224 = MkNID 1102

public export
NID_hmac_sha3_256 : NID
NID_hmac_sha3_256 = MkNID 1103

public export
NID_hmac_sha3_384 : NID
NID_hmac_sha3_384 = MkNID 1104

public export
NID_hmac_sha3_512 : NID
NID_hmac_sha3_512 = MkNID 1105

public export
NID_dsa_with_SHA384 : NID
NID_dsa_with_SHA384 = MkNID 1106

public export
NID_dsa_with_SHA512 : NID
NID_dsa_with_SHA512 = MkNID 1107

public export
NID_dsa_with_SHA3_224 : NID
NID_dsa_with_SHA3_224 = MkNID 1108

public export
NID_dsa_with_SHA3_256 : NID
NID_dsa_with_SHA3_256 = MkNID 1109

public export
NID_dsa_with_SHA3_384 : NID
NID_dsa_with_SHA3_384 = MkNID 1110

public export
NID_dsa_with_SHA3_512 : NID
NID_dsa_with_SHA3_512 = MkNID 1111

public export
NID_ecdsa_with_SHA3_224 : NID
NID_ecdsa_with_SHA3_224 = MkNID 1112

public export
NID_ecdsa_with_SHA3_256 : NID
NID_ecdsa_with_SHA3_256 = MkNID 1113

public export
NID_ecdsa_with_SHA3_384 : NID
NID_ecdsa_with_SHA3_384 = MkNID 1114

public export
NID_ecdsa_with_SHA3_512 : NID
NID_ecdsa_with_SHA3_512 = MkNID 1115

public export
NID_RSA_SHA3_224 : NID
NID_RSA_SHA3_224 = MkNID 1116

public export
NID_RSA_SHA3_256 : NID
NID_RSA_SHA3_256 = MkNID 1117

public export
NID_RSA_SHA3_384 : NID
NID_RSA_SHA3_384 = MkNID 1118

public export
NID_RSA_SHA3_512 : NID
NID_RSA_SHA3_512 = MkNID 1119

public export
NID_aria_128_ccm : NID
NID_aria_128_ccm = MkNID 1120

public export
NID_aria_192_ccm : NID
NID_aria_192_ccm = MkNID 1121

public export
NID_aria_256_ccm : NID
NID_aria_256_ccm = MkNID 1122

public export
NID_aria_128_gcm : NID
NID_aria_128_gcm = MkNID 1123

public export
NID_aria_192_gcm : NID
NID_aria_192_gcm = MkNID 1124

public export
NID_aria_256_gcm : NID
NID_aria_256_gcm = MkNID 1125

public export
NID_ffdhe2048 : NID
NID_ffdhe2048 = MkNID 1126

public export
NID_ffdhe3072 : NID
NID_ffdhe3072 = MkNID 1127

public export
NID_ffdhe4096 : NID
NID_ffdhe4096 = MkNID 1128

public export
NID_ffdhe6144 : NID
NID_ffdhe6144 = MkNID 1129

public export
NID_ffdhe8192 : NID
NID_ffdhe8192 = MkNID 1130

public export
NID_cmcCA : NID
NID_cmcCA = MkNID 1131

public export
NID_cmcRA : NID
NID_cmcRA = MkNID 1132

public export
NID_sm4_ecb : NID
NID_sm4_ecb = MkNID 1133

public export
NID_sm4_cbc : NID
NID_sm4_cbc = MkNID 1134

public export
NID_sm4_ofb128 : NID
NID_sm4_ofb128 = MkNID 1135

public export
NID_sm4_cfb1 : NID
NID_sm4_cfb1 = MkNID 1136

public export
NID_sm4_cfb128 : NID
NID_sm4_cfb128 = MkNID 1137

public export
NID_sm4_cfb8 : NID
NID_sm4_cfb8 = MkNID 1138

public export
NID_sm4_ctr : NID
NID_sm4_ctr = MkNID 1139

public export
NID_ISO_CN : NID
NID_ISO_CN = MkNID 1140

public export
NID_oscca : NID
NID_oscca = MkNID 1141

public export
NID_sm_scheme : NID
NID_sm_scheme = MkNID 1142

public export
NID_sm3 : NID
NID_sm3 = MkNID 1143

public export
NID_sm3WithRSAEncryption : NID
NID_sm3WithRSAEncryption = MkNID 1144

public export
NID_sha512_224WithRSAEncryption : NID
NID_sha512_224WithRSAEncryption = MkNID 1145

public export
NID_sha512_256WithRSAEncryption : NID
NID_sha512_256WithRSAEncryption = MkNID 1146

public export
NID_id_tc26_gost_3410_2012_256_constants : NID
NID_id_tc26_gost_3410_2012_256_constants = MkNID 1147

public export
NID_id_tc26_gost_3410_2012_256_paramSetA : NID
NID_id_tc26_gost_3410_2012_256_paramSetA = MkNID 1148

public export
NID_id_tc26_gost_3410_2012_512_paramSetC : NID
NID_id_tc26_gost_3410_2012_512_paramSetC = MkNID 1149

public export
NID_ISO_UA : NID
NID_ISO_UA = MkNID 1150

public export
NID_ua_pki : NID
NID_ua_pki = MkNID 1151

public export
NID_dstu28147 : NID
NID_dstu28147 = MkNID 1152

public export
NID_dstu28147_ofb : NID
NID_dstu28147_ofb = MkNID 1153

public export
NID_dstu28147_cfb : NID
NID_dstu28147_cfb = MkNID 1154

public export
NID_dstu28147_wrap : NID
NID_dstu28147_wrap = MkNID 1155

public export
NID_hmacWithDstu34311 : NID
NID_hmacWithDstu34311 = MkNID 1156

public export
NID_dstu34311 : NID
NID_dstu34311 = MkNID 1157

public export
NID_dstu4145le : NID
NID_dstu4145le = MkNID 1158

public export
NID_dstu4145be : NID
NID_dstu4145be = MkNID 1159

public export
NID_uacurve0 : NID
NID_uacurve0 = MkNID 1160

public export
NID_uacurve1 : NID
NID_uacurve1 = MkNID 1161

public export
NID_uacurve2 : NID
NID_uacurve2 = MkNID 1162

public export
NID_uacurve3 : NID
NID_uacurve3 = MkNID 1163

public export
NID_uacurve4 : NID
NID_uacurve4 = MkNID 1164

public export
NID_uacurve5 : NID
NID_uacurve5 = MkNID 1165

public export
NID_uacurve6 : NID
NID_uacurve6 = MkNID 1166

public export
NID_uacurve7 : NID
NID_uacurve7 = MkNID 1167

public export
NID_uacurve8 : NID
NID_uacurve8 = MkNID 1168

public export
NID_uacurve9 : NID
NID_uacurve9 = MkNID 1169

public export
NID_ieee : NID
NID_ieee = MkNID 1170

public export
NID_ieee_siswg : NID
NID_ieee_siswg = MkNID 1171

public export
NID_sm2 : NID
NID_sm2 = MkNID 1172

public export
NID_id_tc26_cipher_gostr3412_2015_magma : NID
NID_id_tc26_cipher_gostr3412_2015_magma = MkNID 1173

public export
NID_magma_ctr_acpkm : NID
NID_magma_ctr_acpkm = MkNID 1174

public export
NID_magma_ctr_acpkm_omac : NID
NID_magma_ctr_acpkm_omac = MkNID 1175

public export
NID_id_tc26_cipher_gostr3412_2015_kuznyechik : NID
NID_id_tc26_cipher_gostr3412_2015_kuznyechik = MkNID 1176

public export
NID_kuznyechik_ctr_acpkm : NID
NID_kuznyechik_ctr_acpkm = MkNID 1177

public export
NID_kuznyechik_ctr_acpkm_omac : NID
NID_kuznyechik_ctr_acpkm_omac = MkNID 1178

public export
NID_id_tc26_wrap : NID
NID_id_tc26_wrap = MkNID 1179

public export
NID_id_tc26_wrap_gostr3412_2015_magma : NID
NID_id_tc26_wrap_gostr3412_2015_magma = MkNID 1180

public export
NID_magma_kexp15 : NID
NID_magma_kexp15 = MkNID 1181

public export
NID_id_tc26_wrap_gostr3412_2015_kuznyechik : NID
NID_id_tc26_wrap_gostr3412_2015_kuznyechik = MkNID 1182

public export
NID_kuznyechik_kexp15 : NID
NID_kuznyechik_kexp15 = MkNID 1183

public export
NID_id_tc26_gost_3410_2012_256_paramSetB : NID
NID_id_tc26_gost_3410_2012_256_paramSetB = MkNID 1184

public export
NID_id_tc26_gost_3410_2012_256_paramSetC : NID
NID_id_tc26_gost_3410_2012_256_paramSetC = MkNID 1185

public export
NID_id_tc26_gost_3410_2012_256_paramSetD : NID
NID_id_tc26_gost_3410_2012_256_paramSetD = MkNID 1186

public export
NID_magma_ecb : NID
NID_magma_ecb = MkNID 1187

public export
NID_magma_ctr : NID
NID_magma_ctr = MkNID 1188

public export
NID_magma_ofb : NID
NID_magma_ofb = MkNID 1189

public export
NID_magma_cbc : NID
NID_magma_cbc = MkNID 1190

public export
NID_magma_cfb : NID
NID_magma_cfb = MkNID 1191

public export
NID_magma_mac : NID
NID_magma_mac = MkNID 1192

public export
NID_hmacWithSHA512_224 : NID
NID_hmacWithSHA512_224 = MkNID 1193

public export
NID_hmacWithSHA512_256 : NID
NID_hmacWithSHA512_256 = MkNID 1194

public export
NID_gmac : NID
NID_gmac = MkNID 1195

public export
NID_kmac128 : NID
NID_kmac128 = MkNID 1196

public export
NID_kmac256 : NID
NID_kmac256 = MkNID 1197

public export
NID_aes_128_siv : NID
NID_aes_128_siv = MkNID 1198

public export
NID_aes_192_siv : NID
NID_aes_192_siv = MkNID 1199

public export
NID_aes_256_siv : NID
NID_aes_256_siv = MkNID 1200

public export
NID_blake2bmac : NID
NID_blake2bmac = MkNID 1201

public export
NID_blake2smac : NID
NID_blake2smac = MkNID 1202

public export
NID_sshkdf : NID
NID_sshkdf = MkNID 1203

public export
NID_SM2_with_SM3 : NID
NID_SM2_with_SM3 = MkNID 1204

public export
NID_sskdf : NID
NID_sskdf = MkNID 1205

public export
NID_x963kdf : NID
NID_x963kdf = MkNID 1206

public export
NID_x942kdf : NID
NID_x942kdf = MkNID 1207

public export
NID_id_on_SmtpUTF8Mailbox : NID
NID_id_on_SmtpUTF8Mailbox = MkNID 1208

public export
NID_XmppAddr : NID
NID_XmppAddr = MkNID 1209

public export
NID_SRVName : NID
NID_SRVName = MkNID 1210

public export
NID_NAIRealm : NID
NID_NAIRealm = MkNID 1211

public export
NID_modp_1536 : NID
NID_modp_1536 = MkNID 1212

public export
NID_modp_2048 : NID
NID_modp_2048 = MkNID 1213

public export
NID_modp_3072 : NID
NID_modp_3072 = MkNID 1214

public export
NID_modp_4096 : NID
NID_modp_4096 = MkNID 1215

public export
NID_modp_6144 : NID
NID_modp_6144 = MkNID 1216

public export
NID_modp_8192 : NID
NID_modp_8192 = MkNID 1217

public export
NID_kx_gost18 : NID
NID_kx_gost18 = MkNID 1218

public export
NID_cmcArchive : NID
NID_cmcArchive = MkNID 1219

public export
NID_id_kp_bgpsec_router : NID
NID_id_kp_bgpsec_router = MkNID 1220

public export
NID_id_kp_BrandIndicatorforMessageIdentification : NID
NID_id_kp_BrandIndicatorforMessageIdentification = MkNID 1221

public export
NID_cmKGA : NID
NID_cmKGA = MkNID 1222

public export
NID_id_it_caCerts : NID
NID_id_it_caCerts = MkNID 1223

public export
NID_id_it_rootCaKeyUpdate : NID
NID_id_it_rootCaKeyUpdate = MkNID 1224

public export
NID_id_it_certReqTemplate : NID
NID_id_it_certReqTemplate = MkNID 1225

public export
NID_OGRNIP : NID
NID_OGRNIP = MkNID 1226

public export
NID_classSignTool : NID
NID_classSignTool = MkNID 1227

public export
NID_classSignToolKC1 : NID
NID_classSignToolKC1 = MkNID 1228

public export
NID_classSignToolKC2 : NID
NID_classSignToolKC2 = MkNID 1229

public export
NID_classSignToolKC3 : NID
NID_classSignToolKC3 = MkNID 1230

public export
NID_classSignToolKB1 : NID
NID_classSignToolKB1 = MkNID 1231

public export
NID_classSignToolKB2 : NID
NID_classSignToolKB2 = MkNID 1232

public export
NID_classSignToolKA1 : NID
NID_classSignToolKA1 = MkNID 1233

public export
NID_id_ct_routeOriginAuthz : NID
NID_id_ct_routeOriginAuthz = MkNID 1234

public export
NID_id_ct_rpkiManifest : NID
NID_id_ct_rpkiManifest = MkNID 1235

public export
NID_id_ct_rpkiGhostbusters : NID
NID_id_ct_rpkiGhostbusters = MkNID 1236

public export
NID_id_ct_resourceTaggedAttest : NID
NID_id_ct_resourceTaggedAttest = MkNID 1237

public export
NID_id_cp : NID
NID_id_cp = MkNID 1238

public export
NID_sbgp_ipAddrBlockv2 : NID
NID_sbgp_ipAddrBlockv2 = MkNID 1239

public export
NID_sbgp_autonomousSysNumv2 : NID
NID_sbgp_autonomousSysNumv2 = MkNID 1240

public export
NID_ipAddr_asNumber : NID
NID_ipAddr_asNumber = MkNID 1241

public export
NID_ipAddr_asNumberv2 : NID
NID_ipAddr_asNumberv2 = MkNID 1242

public export
NID_rpkiManifest : NID
NID_rpkiManifest = MkNID 1243

public export
NID_signedObject : NID
NID_signedObject = MkNID 1244

public export
NID_rpkiNotify : NID
NID_rpkiNotify = MkNID 1245

public export
NID_id_ct_geofeedCSVwithCRLF : NID
NID_id_ct_geofeedCSVwithCRLF = MkNID 1246

