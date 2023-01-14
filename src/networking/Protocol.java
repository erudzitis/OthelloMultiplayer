package src.networking;

public class Protocol {
    private static final String HELLO = "HELLO";
    private static final String SEPERATOR = "~";


    /**
     * Enforcing that an instance can't be created of this class
     */
    private Protocol() {}

    /**
     * Protocol method that formats user's desire to claim a username to the src.server accordingly.
     *
     * @param username String, desired username
     * @return String, formatted protocol message
     */
    // TODO: Implement extensions
    public static String claimUsername(String username) {
        return HELLO + SEPERATOR + username;
    }
}
