import publication from '@/content/publication.json';
export function PublicationLinks() {
  const links = publication.links as { label: string; url: string | null }[];
  const arxiv = links.find((link) => link.label === 'arXiv');
  const availablePublications = links.filter(
    (link) => link.label !== 'arXiv' && link.url,
  );
  const wordmark = (
    // oxlint-disable-next-line next/no-img-element -- Preserve the small official local image unchanged in the static export.
    <img
      src="/images/arxiv-logo.jpg"
      alt="arXiv"
      width={800}
      height={504}
    />
  );
  return (
    <div className="publication-links">
      {arxiv?.url ? (
        <a
          className="arxiv-badge"
          href={arxiv.url}
          target="_blank"
          rel="noopener noreferrer"
          referrerPolicy="no-referrer"
          aria-label="Read the paper on arXiv"
        >
          {wordmark}
        </a>
      ) : (
        <span className="arxiv-badge">{wordmark}</span>
      )}
      {availablePublications.map((link) => (
        <a
          key={link.label}
          href={link.url ?? undefined}
          target="_blank"
          rel="noopener noreferrer"
          referrerPolicy="no-referrer"
        >
          {link.label} ↗
        </a>
      ))}
    </div>
  );
}
