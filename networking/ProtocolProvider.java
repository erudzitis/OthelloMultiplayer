package networking;

public class ProtocolProvider {
    private static final String HELLO = "HELLO";
    private static final String SEPERATOR = "~";


    /**
     * Enforcing that an instance can't be created of this class
     */
    private ProtocolProvider() {}

    /**
     * Protocol method that formats user's desire to claim a username to the server accordingly.
     *
     * @param username String, desired username
     * @return String, formatted protocol message
     */
    // TODO: Implement extensions
    public static String claimUsername(String username) {
        return HELLO + SEPERATOR + username;
    }
}
